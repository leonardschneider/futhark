{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant lambda" #-}

-- | @futhark repl@
module Futhark.CLI.REPL (main) where

import Control.Exception hiding (try)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Free.Church
import Control.Monad.State
import Data.Char
import Data.List (intercalate, intersperse)
import qualified Data.List.NonEmpty as NE
import Data.Maybe
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Version
import Futhark.Compiler
import Futhark.MonadFreshNames
import Futhark.Pipeline
import Futhark.Util (fancyTerminal, toPOSIX)
import Futhark.Util.Options
import Futhark.Version
import Language.Futhark hiding (Value, matchDims)
import qualified Language.Futhark.Interpreter as I
import Language.Futhark.Parser hiding (EOF)
import qualified Language.Futhark.Semantic as T
import qualified Language.Futhark.TypeChecker as T
import NeatInterpolation (text)
import qualified System.Console.Haskeline as Haskeline
import System.Directory
import System.FilePath
import Text.Read (readMaybe)
import Data.Array
import qualified Data.ByteString.Lazy.Char8 as C
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.UTF8 as BLU
import Data.ByteString.Builder
import Text.Megaparsec
import Futhark.IR.Primitive (valueIntegral)
import System.Process (CreateProcess (delegate_ctlc), withCreateProcess, waitForProcess, proc)
import qualified Data.Map as M
import GHC.IO.Exception (ExitCode(ExitSuccess, ExitFailure))
import Data.Void
import Data.String
import Data.Functor
import Data.Bits
import Text.Megaparsec.Char
import Control.Arrow hiding ((<+>))
import Data.Either
import Data.Binary (encode)
import System.Console.Haskeline (completeFilename)

banner :: String
banner =
  unlines
    [ "|// |\\    |   |\\  |\\   /",
      "|/  | \\   |\\  |\\  |/  /",
      "|   |  \\  |/  |   |\\  \\",
      "|   |   \\ |   |   | \\  \\"
    ]

-- | Run @futhark repl@.
main :: String -> [String] -> IO ()
main = mainWithOptions () [] "options... [program.fut]" run
  where
    run [] _ = Just $ repl Nothing
    run [prog] _ = Just $ repl $ Just prog
    run _ _ = Nothing

data StopReason = EOF | Stop | Exit | Load FilePath | Interrupt

repl :: Maybe FilePath -> IO ()
repl maybe_prog = do
  when fancyTerminal $ do
    putStr banner
    putStrLn $ "Version " ++ showVersion version ++ "."
    putStrLn "Copyright (C) DIKU, University of Copenhagen, released under the ISC license."
    putStrLn ""
    putStrLn "Run :help for a list of commands."
    putStrLn ""

  let toploop s = do
        (stop, s') <-
          Haskeline.handleInterrupt (pure (Left Interrupt, s))
            . Haskeline.withInterrupt
            $ runStateT (runExceptT $ runFutharkiM $ forever readEvalPrint) s

        case stop of
          Left Stop -> finish s'
          Left EOF -> finish s'
          Left Exit -> finish s'
          Left Interrupt -> do
            liftIO $ T.putStrLn "Interrupted"
            toploop s' {futharkiCount = futharkiCount s' + 1}
          Left (Load file) -> do
            liftIO $ T.putStrLn $ "Loading " <> T.pack file
            maybe_new_state <-
              liftIO $ newFutharkiState (futharkiCount s) $ Just file
            case maybe_new_state of
              Right new_state -> toploop new_state
              Left err -> do
                liftIO $ putStrLn err
                toploop s'
          Right _ -> return ()

      finish s = do
        quit <- if fancyTerminal then confirmQuit else pure True
        if quit then return () else toploop s

  maybe_init_state <- liftIO $ newFutharkiState 0 maybe_prog
  s <- case maybe_init_state of
    Left prog_err -> do
      noprog_init_state <- liftIO $ newFutharkiState 0 Nothing
      case noprog_init_state of
        Left err ->
          error $ "Failed to initialise interpreter state: " ++ err
        Right s -> do
          liftIO $ putStrLn prog_err
          return s {futharkiLoaded = maybe_prog}
    Right s ->
      return s
  home <- getHomeDirectory
  let historyFile = home </> ".futhark" </> "history"
  createDirectoryIfMissing False $ home </> ".futhark"

  let settings = Haskeline.Settings {
          complete = completeFilename,
          historyFile = Just historyFile ,
          autoAddHistory = True
        }
  Haskeline.runInputT settings $ toploop s

  putStrLn "Leaving 'futhark repl'."

confirmQuit :: Haskeline.InputT IO Bool
confirmQuit = do
  c <- Haskeline.getInputChar "Quit REPL? (y/n) "
  case c of
    Nothing -> return True -- EOF
    Just 'y' -> return True
    Just 'n' -> return False
    _ -> confirmQuit

-- | Representation of breaking at a breakpoint, to allow for
-- navigating through the stack frames and such.
data Breaking = Breaking
  { breakingStack :: NE.NonEmpty I.StackFrame,
    -- | Index of the current breakpoint (with
    -- 0 being the outermost).
    breakingAt :: Int
  }

data FutharkiState = FutharkiState
  { futharkiImports :: Imports,
    futharkiNameSource :: VNameSource,
    futharkiCount :: Int,
    futharkiEnv :: (T.Env, I.Ctx),
    -- | Are we currently stopped at a breakpoint?
    futharkiBreaking :: Maybe Breaking,
    -- | Skip breakpoints at these locations.
    futharkiSkipBreaks :: [Loc],
    futharkiBreakOnNaN :: Bool,
    -- | The currently loaded file.
    futharkiLoaded :: Maybe FilePath
  }

newFutharkiState :: Int -> Maybe FilePath -> IO (Either String FutharkiState)
newFutharkiState count0 maybe_file = runExceptT $ do
  (imports, src, tenv, ienv) <- case maybe_file of
    Nothing -> do
      -- Load the builtins through the type checker.
      (_, imports, src) <- badOnLeft show =<< runExceptT (readLibrary [] [])
      -- Then into the interpreter.
      ienv <-
        foldM
          (\ctx -> badOnLeft show <=< runInterpreter' . I.interpretImport ctx)
          I.initialCtx
          $ map (fmap fileProg) imports

      -- Then make the prelude available in the type checker.
      (tenv, d, src') <-
        badOnLeft pretty . snd $
          T.checkDec imports src T.initialEnv (T.mkInitialImport ".") $
            mkOpen "/prelude/prelude"
      -- Then in the interpreter.
      ienv' <- badOnLeft show =<< runInterpreter' (I.interpretDec ienv d)
      return (imports, src', tenv, ienv')
    Just file -> do
      (ws, imports, src) <-
        badOnLeft show
          =<< liftIO
            ( runExceptT (readProgram [] file)
                `catch` \(err :: IOException) ->
                  return (externalErrorS (show err))
            )
      liftIO $ putStrLn $ pretty ws

      let imp = T.mkInitialImport "."
      ienv1 <-
        foldM (\ctx -> badOnLeft show <=< runInterpreter' . I.interpretImport ctx) I.initialCtx $
          map (fmap fileProg) imports
      (tenv1, d1, src') <-
        badOnLeft pretty . snd . T.checkDec imports src T.initialEnv imp $
          mkOpen "/prelude/prelude"
      (tenv2, d2, src'') <-
        badOnLeft pretty . snd . T.checkDec imports src' tenv1 imp $
          mkOpen $ toPOSIX $ dropExtension file
      ienv2 <- badOnLeft show =<< runInterpreter' (I.interpretDec ienv1 d1)
      ienv3 <- badOnLeft show =<< runInterpreter' (I.interpretDec ienv2 d2)
      return (imports, src'', tenv2, ienv3)

  return
    FutharkiState
      { futharkiImports = imports,
        futharkiNameSource = src,
        futharkiCount = count0,
        futharkiEnv = (tenv, ienv),
        futharkiBreaking = Nothing,
        futharkiSkipBreaks = mempty,
        futharkiBreakOnNaN = False,
        futharkiLoaded = maybe_file
      }
  where
    badOnLeft :: (err -> String) -> Either err a -> ExceptT String IO a
    badOnLeft _ (Right x) = return x
    badOnLeft p (Left err) = throwError $ p err

getPrompt :: FutharkiM String
getPrompt = do
  i <- gets futharkiCount
  return $ "[" ++ show i ++ "]> "

mkOpen :: FilePath -> UncheckedDec
mkOpen f = OpenDec (ModImport f NoInfo mempty) mempty

-- The ExceptT part is more of a continuation, really.
newtype FutharkiM a = FutharkiM {runFutharkiM :: ExceptT StopReason (StateT FutharkiState (Haskeline.InputT IO)) a}
  deriving
    ( Functor,
      Applicative,
      Monad,
      MonadState FutharkiState,
      MonadIO,
      MonadError StopReason
    )

readEvalPrint :: FutharkiM ()
readEvalPrint = do
  prompt <- getPrompt
  line <- inputLine prompt
  breaking <- gets futharkiBreaking
  case T.uncons line of
    Nothing
      | isJust breaking -> throwError Stop
      | otherwise -> return ()
    Just (':', command) -> do
      let (cmdname, rest) = T.break isSpace command
          arg = T.dropWhileEnd isSpace $ T.dropWhile isSpace rest
      case filter ((cmdname `T.isPrefixOf`) . fst) commands of
        [] -> liftIO $ T.putStrLn $ "Unknown command '" <> cmdname <> "'"
        [(_, (cmdf, _))] -> cmdf arg
        matches ->
          liftIO . T.putStrLn $
            "Ambiguous command; could be one of "
              <> mconcat (intersperse ", " (map fst matches))
    _ -> do
      -- Read a declaration or expression.
      maybe_dec_or_e <- parseDecOrExpIncrM (inputLine "  ") prompt line

      case maybe_dec_or_e of
        Left err -> liftIO $ print err
        Right (Left d) -> onDec d
        Right (Right e) -> onExp e
  modify $ \s -> s {futharkiCount = futharkiCount s + 1}
  where
    inputLine prompt = do
      inp <- FutharkiM $ lift $ lift $ Haskeline.getInputLine prompt
      case inp of
        Just s -> return $ T.pack s
        Nothing -> throwError EOF

getIt :: FutharkiM (Imports, VNameSource, T.Env, I.Ctx)
getIt = do
  imports <- gets futharkiImports
  src <- gets futharkiNameSource
  (tenv, ienv) <- gets futharkiEnv
  return (imports, src, tenv, ienv)

onDec :: UncheckedDec -> FutharkiM ()
onDec d = do
  (imports, src, tenv, ienv) <- getIt
  cur_import <- gets $ T.mkInitialImport . fromMaybe "." . futharkiLoaded

  -- Most of the complexity here concerns the dealing with the fact
  -- that 'import "foo"' is a declaration.  We have to involve a lot
  -- of machinery to load this external code before executing the
  -- declaration itself.
  let basis = Basis imports src ["/prelude/prelude"]
      mkImport = uncurry $ T.mkImportFrom cur_import
  imp_r <- runExceptT $ readImports basis (map mkImport $ decImports d)

  case imp_r of
    Left e -> liftIO $ print e
    Right (_, imports', src') ->
      case T.checkDec imports' src' tenv cur_import d of
        (_, Left e) -> liftIO $ putStrLn $ pretty e
        (_, Right (tenv', d', src'')) -> do
          let new_imports = filter ((`notElem` map fst imports) . fst) imports'
          int_r <- runInterpreter $ do
            let onImport ienv' (s, imp) =
                  I.interpretImport ienv' (s, T.fileProg imp)
            ienv' <- foldM onImport ienv new_imports
            I.interpretDec ienv' d'
          case int_r of
            Left err -> liftIO $ print err
            Right ienv' -> modify $ \s ->
              s
                { futharkiEnv = (tenv', ienv'),
                  futharkiImports = imports',
                  futharkiNameSource = src''
                }

onExp :: UncheckedExp -> FutharkiM ()
onExp e = do
  (imports, src, tenv, ienv) <- getIt
  case T.checkExp imports src tenv e of
    (_, Left err) -> liftIO $ putStrLn $ pretty err
    (_, Right (tparams, e'))
      | null tparams -> do
        r <- runInterpreter $ I.interpretExp ienv e'
        do process e' r
      | otherwise -> liftIO $ do
        putStrLn $ "Inferred type of expression: " ++ pretty (typeOf e')
        putStrLn $
          "The following types are ambiguous: "
            ++ intercalate ", " (map (prettyName . typeParamName) tparams)
  where
    process :: Exp -> Either I.InterpreterError I.Value -> FutharkiM ()
    process _ (Left err) = liftIO $ print err
    process (Attr (AttrAtom (AtomName "proc") _) _ _) (Right (I.ValueRecord m)) =
      exec cmd args
      where
        cmd = head vs
        args = tail vs
        vs = map (C.unpack . msg) $ M.elems m
    process (Attr (AttrAtom (AtomName "raw") _) _ _) (Right vs@(I.ValueArray _ _)) =
      liftIO $ do C.putStrLn $ msg vs
    process (Attr (AttrAtom (AtomName "proc") _) _ _) (Right vs@(I.ValueArray _ _)) =
      exec cmd []
        where
        cmd = C.unpack $ msg vs
    process (Attr (AttrAtom (AtomName "ast") _) v _) _ =
      liftIO $ do print v
    process _ (Right v) =
      liftIO $ putStrLn $ pretty v
    msg (I.ValueArray _ vs) = BL.pack $ map (fromIntegral . getValue) $ elems vs
    msg _ = error "Value type not supported"
    getValue (I.ValuePrim (UnsignedValue v)) = valueIntegral v
    getValue (I.ValuePrim (SignedValue v)) = valueIntegral v
    getValue _ = error "Value type not supported"
    exec cmd args = liftIO $ do
      exit_code <- withCreateProcess (proc cmd args) { delegate_ctlc = True } $ \_ _ _ p ->
        waitForProcess p
      case exit_code of
        ExitSuccess   -> return ()
        ExitFailure _ -> putStrLn $ "Process failed with exit code " ++ show exit_code

prettyBreaking :: Breaking -> String
prettyBreaking b =
  prettyStacktrace (breakingAt b) $ map locStr $ NE.toList $ breakingStack b

-- Are we currently willing to break for this reason?  Among othe
-- things, we do not want recursive breakpoints.  It could work fine
-- technically, but is probably too confusing to be useful.
breakForReason :: FutharkiState -> I.StackFrame -> I.BreakReason -> Bool
breakForReason s _ I.BreakNaN
  | not $ futharkiBreakOnNaN s = False
breakForReason s top _ =
  isNothing (futharkiBreaking s)
    && locOf top `notElem` futharkiSkipBreaks s

runInterpreter :: F I.ExtOp a -> FutharkiM (Either I.InterpreterError a)
runInterpreter m = runF m (return . Right) intOp
  where
    intOp (I.ExtOpError err) =
      return $ Left err
    intOp (I.ExtOpTrace w v c) = do
      liftIO $ putStrLn $ w ++ ": " ++ v
      c
    intOp (I.ExtOpBreak w why callstack c) = do
      s <- get

      let why' = case why of
            I.BreakPoint -> "Breakpoint"
            I.BreakNaN -> "NaN produced"
          top = NE.head callstack
          ctx = I.stackFrameCtx top
          tenv = I.typeCheckerEnv $ I.ctxEnv ctx
          breaking = Breaking callstack 0

      -- Are we supposed to respect this breakpoint?
      when (breakForReason s top why) $ do
        liftIO $ putStrLn $ why' <> " at " ++ locStr w
        liftIO $ putStrLn $ prettyBreaking breaking
        liftIO $ putStrLn "<Enter> to continue."

        -- Note the cleverness to preserve the Haskeline session (for
        -- line history and such).
        (stop, s') <-
          FutharkiM . lift . lift $
            runStateT
              (runExceptT $ runFutharkiM $ forever readEvalPrint)
              s
                { futharkiEnv = (tenv, ctx),
                  futharkiCount = futharkiCount s + 1,
                  futharkiBreaking = Just breaking
                }

        case stop of
          Left (Load file) -> throwError $ Load file
          _ -> do
            liftIO $ putStrLn "Continuing..."
            put
              s
                { futharkiCount =
                    futharkiCount s',
                  futharkiSkipBreaks =
                    futharkiSkipBreaks s' <> futharkiSkipBreaks s,
                  futharkiBreakOnNaN =
                    futharkiBreakOnNaN s'
                }

      c

runInterpreter' :: MonadIO m => F I.ExtOp a -> m (Either I.InterpreterError a)
runInterpreter' m = runF m (return . Right) intOp
  where
    intOp (I.ExtOpError err) = return $ Left err
    intOp (I.ExtOpTrace w v c) = do
      liftIO $ putStrLn $ w ++ ": " ++ v
      c
    intOp (I.ExtOpBreak _ _ _ c) = c

type Command = T.Text -> FutharkiM ()

loadCommand :: Command
loadCommand file = do
  loaded <- gets futharkiLoaded
  case (T.null file, loaded) of
    (True, Just loaded') -> throwError $ Load loaded'
    (True, Nothing) -> liftIO $ T.putStrLn "No file specified and no file previously loaded."
    (False, _) -> throwError $ Load $ T.unpack file

-- Print a la Python, formatted string literal
-- Supported specifiers:
-- s: utf-8 string (for arrays)
-- x: hexadecimal
-- X: hexadecimal
-- b: binary
-- d: decimal
-- #: prefix 0x, 0X, 0b resp. x, X, b
-- [..fmt sep..]: separator for arrays; can be nested
-- (fmt1, fmt2, ...): format for tuples 
-- $: type suffix; can be placed after array, tuple or after value specifier
-- Examples
-- > let str = "foo"
-- > :print "as array: {str}"
-- as array: [102u8, 111u8, 111u8]
-- > :print "as array: {str:[..d$, ..]}"
-- as array: [102u8, 111u8, 111u8]
-- > :print "as array with top level type: {str:[..d, ..]$}"
-- as array with top level type: [102, 111, 111][3]u8
-- > :print "as array of plain decimals: {str:[..d, ..]}"
-- as array of plain decimals: [102, 111, 111]
-- > :print "as array of hex: {str:[..#X, ..]}"
-- as array of hex: [0X66, 0X6F, 0X6F]
-- > :print "as upper hex string: {str:X}"
-- as upper hex string: 666F6F
-- > :print "as lower hex string: {str:x}"
-- as lower hex string: 666f6f
-- > :print "as string: {str:s}"
-- as string: foo
-- > let strint = ("foo", [1i32, 42i32])
-- > :print "tuple: {strint:(0:[..d$, ..], 1:[..#x$, ..])}"
-- tuple: ([102u8, 111u8, 111u8], [0x00000001u32, 0x0000002au32])

-- Data structures
data FormatType = FormatStr | FormatBin | FormatHex | FormatHeX | FormatDec deriving Show

data Format =
  FormatArray {
    lbracket :: String,
    fmt:: Format,
    sep :: String,
    rbracket:: String,
    suffix :: Bool
  } |
  FormatValue {
    prefix :: Bool,
    ftype :: FormatType,
    suffix :: Bool
  } deriving Show
data FormatExp = FormatExp String Format | FormatDefault String | StringPart String deriving Show
type FormatString = [FormatExp]

-- Rendering
printf :: Format -> I.Value -> Either String BL.ByteString
printf = printfmt
  where
  printfmt :: Format -> I.Value -> Either String BL.ByteString
  printfmt (FormatArray {sep, suffix, fmt, lbracket, rbracket}) v@(I.ValueArray _ vs) =
    Right (fromString lbracket) <+>
    fmap (BL.concat . intersperse (fromString sep)) (mapM (printfmt fmt) (elems vs)) <+>
    Right (fromString rbracket) <+>
    showSuffix suffix v
  printfmt fmt@(FormatValue {ftype, suffix, prefix}) arr0@(I.ValueArray _ vs) =
    showPrefix prefix ftype <+>
    fmap BL.concat (mapM (printfmt fmt) (elems vs)) <+>
    showSuffix suffix arr0
  printfmt (FormatValue {prefix=prefix, suffix=suffix, ftype=ftype}) v0@(I.ValuePrim v) =
    showPrefix prefix ftype <+>
    showValue ftype v <+>
    showSuffix suffix v0
  printfmt fmt v =
    Left $ "Don't know how to display value: " <> pretty v <>"\n with format: " <> show fmt

  (<+>) :: (Monoid m) => Either String m -> Either String m -> Either String m
  (<+>) (Left a) (Left b) = Left $ a <> "\n" <> b
  (<+>) (Left a) (Right _) = Left a
  (<+>) (Right _) (Left b) = Left b
  (<+>) (Right a) (Right b) = Right $ a <> b



  showPrefix :: Bool -> FormatType -> Either String BL.ByteString
  showPrefix False _ = Right ""
  showPrefix True FormatHex = Right "0x"
  showPrefix True FormatHeX = Right "0x"
  showPrefix True FormatBin = Right "0b"
  showPrefix True FormatDec = Right ""
  showPrefix True FormatStr = Right ""

  showSuffix :: Bool -> I.Value -> Either String BL.ByteString
  showSuffix False _ = Right ""
  showSuffix True v = showType v

  showType :: I.Value -> Either String BL.ByteString
  showType (I.ValuePrim v@(UnsignedValue _)) = Right (fromString "u") <+> valueSize v
  showType (I.ValuePrim v@(FloatValue _)) = Right (fromString "f") <> valueSize v
  showType (I.ValuePrim (BoolValue _)) = Right (fromString "bool")
  showType (I.ValueArray s vs) = Right (fromString (pretty s)) <+> showType (head $ elems vs)
  showType (I.ValueRecord m)
    | Just vs <- areTupleFields m =
      Right (fromString "(") <+>
      fmap (BL.intercalate (fromString ", ")) (mapM showType vs) <+>
      Right (fromString ")")
    | otherwise =
      Right (fromString "{") <+>
      fmap (BL.intercalate (fromString ", ")) (mapM field (M.toList m)) <+>
      Right (fromString "}")
    where
      field (k, v) = Right (fromString $ nameToString k <> ": ") <+> showType v
  showType (I.ValueSum _ n vs)
    | null vs = Right $ fromString $ "#" <> nameToString n
    | otherwise =
        Right (fromString ("#" <> nameToString n <> " ")) <+>
        fmap BL.concat (mapM showType vs)
  showType v = Right $ fromString $ "Type not found for value: " <> pretty v

  showValue :: FormatType -> PrimValue -> Either String BL.ByteString
  showValue FormatDec (UnsignedValue (Int8Value v)) = Right $ toLazyByteString $ int8Dec v
  showValue FormatDec (UnsignedValue (Int16Value v)) = Right $ toLazyByteString $ int16Dec v
  showValue FormatDec (UnsignedValue (Int32Value v)) = Right $ toLazyByteString $ int32Dec v
  showValue FormatDec (UnsignedValue (Int64Value v)) = Right $ toLazyByteString $ int64Dec v
  showValue FormatDec (FloatValue (Float32Value v)) = Right $ toLazyByteString $ floatDec v
  showValue FormatDec (FloatValue (Float64Value v)) = Right $ toLazyByteString $ doubleDec v
  showValue FormatHex (UnsignedValue (Int8Value v)) = Right $ toLazyByteString $ int8HexFixed v
  showValue FormatHex (UnsignedValue (Int16Value v)) = Right $ toLazyByteString $ int16HexFixed v
  showValue FormatHex (UnsignedValue (Int32Value v)) = Right $ toLazyByteString $ int32HexFixed v
  showValue FormatHex (UnsignedValue (Int64Value v)) = Right $ toLazyByteString $ int64HexFixed v
  showValue FormatHex (FloatValue (Float32Value v)) = Right $ toLazyByteString $ floatHexFixed v
  showValue FormatHex (FloatValue (Float64Value v)) = Right $ toLazyByteString $ doubleHexFixed v
  showValue FormatHeX v@(UnsignedValue _) = C.map toUpper <$> showValue FormatHex v
  showValue FormatBin (UnsignedValue (Int8Value v)) = Right $ BL.concatMap word2bin (encode v)
  showValue FormatStr (UnsignedValue (Int8Value v)) = Right $ encode v
  showValue FormatStr (UnsignedValue (Int16Value v)) = Right $ encode v
  showValue FormatStr (UnsignedValue (Int32Value v)) = Right $ encode v
  showValue FormatStr (UnsignedValue (Int64Value v)) = Right $ encode v
  showValue FormatBin (BoolValue True) = Right $ fromString "1"
  showValue FormatBin (BoolValue False) = Right $ fromString "0"
  showValue ftype (SignedValue v) = showValue ftype (UnsignedValue v)
  showValue ftype v = Left $ "Don't know how to display " <> show ftype <> " format for " <> show v

  word2bin :: Word8 -> BL.ByteString
  word2bin w = BL.pack $ reverse $
    [testBit w i | i <- [0.. finiteBitSize w - 1]] <&> bool2word
    where
      bool2word False = 48 -- ascii '0'
      bool2word True  = 49 -- ascii '1'

  valueSize :: PrimValue -> Either String BL.ByteString
  valueSize (UnsignedValue (Int8Value _)) = Right "8"
  valueSize (UnsignedValue (Int16Value _)) = Right "16"
  valueSize (UnsignedValue (Int32Value _)) = Right "32"
  valueSize (UnsignedValue (Int64Value _)) = Right "64"
  valueSize (SignedValue v) = valueSize (UnsignedValue v)
  valueSize (FloatValue (Float16Value _ )) = Right "16"
  valueSize (FloatValue (Float32Value _ )) = Right "32"
  valueSize (FloatValue (Float64Value _ )) = Right "32"
  valueSize v = Left $ "Cannot find size for: " <> show v

-- Parsing
type Parser = Parsec Void T.Text

formatStringParser :: Parser FormatString
formatStringParser =
  between (char '"') (char '"') (many $ choice [
    try $ StringPart <$> stringPartParser,
    try $ between (char '{') (char '}') repParser
  ])

  where

  repParser =
    choice [
      try $ FormatExp <$> expParser <*> (char ':' *> formatParser),
      try $ FormatDefault <$> expParser
    ]

  expParser = some (try $ satisfy (\c -> c /= ':' && c /= '{' && c/= '}') :: Parser Char)

  formatParser =
    choice [
      try formatValueParser,
      try formatArrayParser
    ]

  formatArrayParser =
    FormatArray <$>
    lbracketParser <*>
    (string ".." *> formatParser) <*>
    sepParser <*>
    (string ".." *> rbracketParser) <*>
    suffixParser

  lbracketParser = many (try $ satisfy (/= '.') :: Parser Char) <?> "lbracket"

  rbracketParser = many (try $ satisfy (\c -> c/= '$' && c /= '}') :: Parser Char) <?> "rbracket"

  formatValueParser =
    FormatValue <$>
    prefixParser <*>
    ftypeParser <*>
    suffixParser

  sepParser = many $
    choice [
      try $ satisfy (/= '.') :: Parser Char,
      try $ char '.' <* notFollowedBy (char '.')
    ]

  prefixParser =
    choice [
      try (char '#') $> True,
      return False :: Parser Bool
    ]
  ftypeParser =
    choice [
      string "x" $> FormatHex,
      string "X" $> FormatHeX,
      string "b" $> FormatBin,
      string "s" $> FormatStr,
      string "d" $> FormatDec
    ]
  suffixParser =
    choice [
      try $ char '$' $> True,
      return False :: Parser Bool
    ]
  stringPartParser = some $
    choice [
      try $ satisfy (\c -> c /= '{' && c /= '}' && c /= '"') :: Parser Char,
      string "{{" $> '{',
      string "}}" $> '}',
      string "\\\"" $> '"'
    ]

evalExp :: Kleisli
  FutharkiM
  T.Text
  (Either String (Warnings, I.Value))
evalExp =
  parseExp "" ^>>
  left (arr show) >>>
  right checkExp >>>
  (arr Left ||| left (arr id)) >>>
  right interpExp >>>
  (arr Left ||| left (arr id))
  where
    checkExp = Kleisli (return getIt) &&& returnA >>^
      \((imports, src, tenv, ienv), e) ->
        case T.checkExp imports src tenv e of
          (warning, Right (tparams, e'))
            | null tparams -> Right (warning, (ienv, e'))
            | otherwise -> Left ("Ambiguous expression: " <> show e)
          (_, Left err) -> Left (pretty err)

    interpExp = second (Kleisli (runInterpreter' . uncurry I.interpretExp)) >>^
      \case
        (warning, Right v) -> Right (warning, v)
        (_, Left err) -> Left (show err)

render :: [FormatExp] -> FutharkiM [Either String (Warnings, BL.ByteString)]
render = mapM \case
  StringPart s -> return $ Right (mempty, BLU.fromString s)
  FormatDefault e -> render' e Nothing
  FormatExp e fmt -> render' e (Just fmt)
  where
    render' e maybeFmt= runKleisli (
        T.pack ^>>
        evalExp >>>
        right (arr $ printf' maybeFmt) >>>
        (arr Left ||| left (arr id))
      ) e
    printf' (Just fmt) (w, v) =
      case printf fmt v of
        Left err -> Left $ pretty w <> "\n" <> err
        Right ls -> Right (w, ls)
    printf' Nothing (w, v) = Right (w, BLU.fromString $ pretty v)

sc :: Parser Char
sc =
  choice [
    char ' ',
    char '\n',
    char '\r',
    char '\t'
  ]

optParser :: ArgOrder a
  -> [OptDescr a]
  -> Parser end
  -> Parser (([a], [String], [String]), end)
optParser argorder opts p =
  (first (getOpt argorder opts) <$> manyTill_ (try $ optionParser <* some (try sc)) (try p)) <* eof
  where
    optionParser = some $
      choice [
        try alphaNumChar,
        try $ char '-',
        try $ char '=',
        try $ char '_',
        try $ char '/'
      ]

data PrintFlag = PrintParse deriving (Show, Eq)

printOptions :: [OptDescr PrintFlag]
printOptions =
  [ Option [] ["parse"] (NoArg PrintParse) "Parse print expression"
  ]

printCommand :: Command
printCommand = runKleisli $
  parse (optParser Permute printOptions formatStringParser) "" ^>>
  optParse ^>>
  right render' >>>
  (Kleisli (liftIO . putStrLn) ||| Kleisli (liftIO . C.putStrLn . BLU.take 10000))
  where
    optParse (Left err) = Left $ errorBundlePretty err
    optParse (Right ((_,_,errs@(_:_)), _)) = Left $ intercalate "\n" errs
    optParse (Right ((flags, _, _), fstring :: FormatString)) =
      if PrintParse `elem` flags then
        Left $ show fstring
      else
        Right fstring
    render' :: Kleisli FutharkiM [FormatExp] BL.ByteString
    render' = Kleisli render >>^ \res ->
      if null $ lefts res then
        let
          (ws, rs) = unzip $ rights res
          wstr = BLU.fromString $ pretty $ mconcat ws
          rstr = BL.concat rs
        in
          if BL.null wstr then
            rstr
          else
            wstr <> "\n" <> rstr
      else
        BLU.fromString $ concat $ lefts res

-- Display Futhark AST for expression or declaration
astCommand :: Command
astCommand = genCommand parseExp T.checkExp $ \(_, e) -> liftIO $ print e

genCommand ::
  Show err =>
  (String -> T.Text -> Either err a) ->
  (Imports -> VNameSource -> T.Env -> a -> (Warnings, Either T.TypeError b)) ->
  (b -> FutharkiM ()) ->
  Command
genCommand f g h e = do
  prompt <- getPrompt
  case f prompt e of
    Left err -> liftIO $ print err
    Right e' -> do
      imports <- gets futharkiImports
      src <- gets futharkiNameSource
      (tenv, _) <- gets futharkiEnv
      case snd $ g imports src tenv e' of
        Left err -> liftIO $ putStrLn $ pretty err
        Right x -> h x

typeCommand :: Command
typeCommand = genCommand parseExp T.checkExp $ \(ps, e) ->
  liftIO $ putStrLn $ pretty e <> concatMap ((" " <>) . pretty) ps
    <> " : "
    <> pretty (typeOf e)

mtypeCommand :: Command
mtypeCommand = genCommand parseModExp T.checkModExp $ \(ps, _) ->
  liftIO $ putStrLn $ pretty ps

unbreakCommand :: Command
unbreakCommand _ = do
  top <- gets $ fmap (NE.head . breakingStack) . futharkiBreaking
  case top of
    Nothing -> liftIO $ putStrLn "Not currently stopped at a breakpoint."
    Just top' -> do
      modify $ \s -> s {futharkiSkipBreaks = locOf top' : futharkiSkipBreaks s}
      throwError Stop

nanbreakCommand :: Command
nanbreakCommand _ = do
  modify $ \s -> s {futharkiBreakOnNaN = not $ futharkiBreakOnNaN s}
  b <- gets futharkiBreakOnNaN
  liftIO $
    putStrLn $
      if b
        then "Now treating NaNs as breakpoints."
        else "No longer treating NaNs as breakpoints."

frameCommand :: Command
frameCommand which = do
  maybe_stack <- gets $ fmap breakingStack . futharkiBreaking
  case (maybe_stack, readMaybe $ T.unpack which) of
    (Just stack, Just i)
      | frame : _ <- NE.drop i stack -> do
        let breaking = Breaking stack i
            ctx = I.stackFrameCtx frame
            tenv = I.typeCheckerEnv $ I.ctxEnv ctx
        modify $ \s ->
          s
            { futharkiEnv = (tenv, ctx),
              futharkiBreaking = Just breaking
            }
        liftIO $ putStrLn $ prettyBreaking breaking
    (Just _, _) ->
      liftIO $ putStrLn $ "Invalid stack index: " ++ T.unpack which
    (Nothing, _) ->
      liftIO $ putStrLn "Not stopped at a breakpoint."

pwdCommand :: Command
pwdCommand _ = liftIO $ putStrLn =<< getCurrentDirectory

cdCommand :: Command
cdCommand dir
  | T.null dir = liftIO $ putStrLn "Usage: ':cd <dir>'."
  | otherwise =
    liftIO $
      setCurrentDirectory (T.unpack dir)
        `catch` \(err :: IOException) -> print err

helpCommand :: Command
helpCommand _ = liftIO $
  forM_ commands $ \(cmd, (_, desc)) -> do
    T.putStrLn $ ":" <> cmd
    T.putStrLn $ T.replicate (1 + T.length cmd) "-"
    T.putStr desc
    T.putStrLn ""
    T.putStrLn ""

quitCommand :: Command
quitCommand _ = throwError Exit

commands :: [(T.Text, (Command, T.Text))]
commands =
  [ ( "load",
      ( loadCommand,
        [text|
Load a Futhark source file.  Usage:

  > :load foo.fut

If the loading succeeds, any expressions entered subsequently can use the
declarations in the source file.

Only one source file can be loaded at a time.  Using the :load command a
second time will replace the previously loaded file.  It will also replace
any declarations entered at the REPL.

|]
      )
    ),
    ( "type",
      ( typeCommand,
        [text|
Show the type of an expression, which must fit on a single line.
|]
      )
    ),
    ( "mtype",
      ( mtypeCommand,
        [text|
Show the type of a module expression, which must fit on a single line.
|]
      )
    ),
    ( "ast",
      ( astCommand,
        [text|
Show the Futhark AST of a declaration or expression.
|]
      )
    ),
    ( "print",
      ( printCommand,
        [text|
Print Futhark expression.
|]
      )
    ),
    ( "unbreak",
      ( unbreakCommand,
        [text|
Skip all future occurences of the current breakpoint.
|]
      )
    ),
    ( "nanbreak",
      ( nanbreakCommand,
        [text|
Toggle treating operators that produce new NaNs as breakpoints.  We consider a NaN
to be "new" if none of the arguments to the operator in question is a NaN.
|]
      )
    ),
    ( "frame",
      ( frameCommand,
        [text|
While at a break point, jump to another stack frame, whose variables can then
be inspected.  Resuming from the breakpoint will jump back to the innermost
stack frame.
|]
      )
    ),
    ( "pwd",
      ( pwdCommand,
        [text|
Print the current working directory.
|]
      )
    ),
    ( "cd",
      ( cdCommand,
        [text|
Change the current working directory.
|]
      )
    ),
    ( "help",
      ( helpCommand,
        [text|
Print a list of commands and a description of their behaviour.
|]
      )
    ),
    ( "quit",
      ( quitCommand,
        [text|
Exit REPL.
|]
      )
    )
  ]
