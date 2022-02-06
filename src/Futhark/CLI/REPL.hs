{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# LANGUAGE BlockArguments #-}

-- | @futhark repl@
module Futhark.CLI.REPL (main) where

import Control.Exception
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
import qualified Data.Array as D
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy as BL
import Futhark.IR.Primitive (valueIntegral)
import System.Process (CreateProcess (delegate_ctlc), withCreateProcess, waitForProcess, proc)
import qualified Data.Map as M
import GHC.IO.Exception (ExitCode(ExitSuccess, ExitFailure))
import Futhark.Test (getExpectedResult)

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
  Haskeline.runInputT Haskeline.defaultSettings $ toploop s

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
newFutharkiState count maybe_file = runExceptT $ do
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
        futharkiCount = count,
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
    msg (I.ValueArray _ vs) = B.pack $ map (fromIntegral . getValue) $ D.elems vs
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
data FormatType = FormatStr | FormatBin | FormatHex | FormatHeX | FormatDec
instance Show FormatType where
  show FormatStr = "string"
  show FormatBin = "binary"
  show FormatHex = "hexadecimal"
  show FormatHeX = "hexadecimal"
  show FormatDec = "decimal"
data Format =
  FormatArray { lbracket :: String, fmt:: Format, sep :: String, rbracket:: String, suffix :: Bool } |
  FormatTuple { start :: String, elems :: [{fmt :: Format, sep :: String}], suffix :: Bool } |
  FormatValue {
    prefix :: Bool,
    ftype :: FormatType,
    suffix :: Bool
  } |
  StringPart String
data FormatExp = FormatExp String Format | FormatDefault String | StringPart String
type FormatString = [FormatExp]
-- Convenient defaults
formatArray = FormatArray {sep="", suffix=False, prefix=False}
formatTuple = FormatTuple {suffix=False}
formatValue = FormatValue {prefix=False, suffix=False}

-- Rendering
printf :: (String -> IO I.Value) -> FormatString -> IO BL.ByteString
printf expint fs = foldM (return $ printfmt expint) BL.empty fs

printfexp :: (String -> IO I.Value) -> FormatExp -> IO BL.ByteString
printfexp _ (FormatDefault v) = return show v
printfexp _ (StringPart s) = return show s
printfexp expint len (FormatExp s fmt) = do
  exp <- expint s
  return printfmt exp fmt

printfmt :: Format -> I.Value -> BL.ByteString
printfmt (FormatArray {sep=sep, suffix=suffix, fmt=fmt, lbracket=lbracket, rbracket=rbracket}) (I.ValueArray _ vs) =
  lbracket <>
  intercalate sep (map (printfmt fmt) elems) <>
  rbracket <>
  showSuffix suffix v
--printfmt (FormatTuple {start=start, elems=elems, suffix=suffix}) (I.ValueRecord vs) =
--  start <>
--  showRecord v elems <>
--  showSuffix suffix v
printfmt fmt@(FormatValue {ftype=ftype, suffix=suffix, prefix=prefix}) (I.ValueArray _ vs) =
  showPrefix prefix ftype <>
  BL.concat $ map (printfmt fmt) vs <>
  showSuffix suffix arr
  --show (FormatValue {value=(I.ValueRecord vs), fmt=fmt, suffix=suffix, prefix=prefix}) =
  --  (showPrefix prefix fmt) ++
  --  (unwords $ (elems vs) <&> (\v -> show $ formatValue {value=v, fmt=fmt})) ++
  --  (showSuffix suffix fmt)
printfmt (FormatValue {prefix=prefix, suffix=suffix, ftype=ftype}) (I.ValuePrim v) =
  showPrefix prefix ftype <>
  showValue v <>
  showSuffix suffix
printfmt _ (FormatValue v) =
  "Don't know how to display value: " <> show v
 
showPrefix :: Bool -> FormatType -> String
showPrefix False _ = ""
showPrefix True FormatHex = "0x"
showPrefix True FormatHeX = "0x"
showPrefix True FormatBin = "0b"
showPrefix True FormatDec = ""
showPrefix True FormatStr = ""

showSuffix :: Bool -> I.Value -> String
showSuffix False _ = ""
showSuffix True v = showType v

showType :: I.Value -> String
showType (PrimValue v@(UnsignedValue _)) = "u" ++ (valueSize v)
showType (PrimValue v@(FloatValue _)) = "f" ++ (valueSize v)
showType (PrimValue v@(BoolValue _)) = "bool"
showType (I.ValueArray s (v: _)) = pretty s ++ (showType v)
showType (I.ValueArray s _) = pretty s
showType (I.ValueRecord m)
  | Just vs <- areTupleFields m =
    "(" ++ (intercalate ", " $ map showType vs) ++ ")"
  | otherwise =
    "{" ++ (intercalate ", " $ map field $ M.toList m) ++ "}"
  where
    field (k, v) = (nameToString k) ++ ": " ++ (showType v)
showType (I.ValueSum _ n vs)
  | numElements vs == 0 = "#" ++ (nameToString n)
  | otherwise = "#" ++ (nameToString n) ++ " " ++ (intercalate " " $ map showType vs)
showType v = "Type not found for value: " ++ (pretty v)

showValue :: FormatType -> I.PrimValue -> String
showValue FormatStr (UnsignedValue v) = C.unpack $ B.pack $ fromIntegral
showValue FormatHex (UnsignedValue v) = show $ hexString $ B.pack $ toLower $ fromIntegral
showValue FormatHeX (UnsignedValue v) = show $ hexString $ B.pack $ toUpper $ fromIntegral
showValue FormatBin (UnsignedValue v) = show $ B.pack $ map word2bin $ fromIntegral
showValue FormatDec (UnsignedValue v) = show v
showValue FormatDec (SignedValue v) = show v
showValue FormatDec (FloatValue v) = show v
showValue FormatDec (BoolValue v) = show v
showValue FormatBin (BoolValue True) = "1"
showValue FormatBin (BoolValue False) = "0" 
showValue ftype (SignedValue v) = showValue ftype (SignedValue v)
showValue ftype v = "Don't know how to display " <> show ftype <> " format for " <> show v

word2bin :: Word8 -> [Word8]
wordbin w =
  [testBit w i | i <- [0.. finiteBitSize w - 1]] <&> bool2word
  where
    bool2word False = fromIntegral 0
    bool2word True = fromIntegral 1

valueSize :: I.PrimValue -> String
valueSize (UnsignedValue (Int8Value _)) = "8"
valueSize (UnsignedValue (Int16Value _)) = "16"
valueSize (UnsignedValue (Int32Value _)) = "32"
valueSize (UnsignedValue (Int64Value _)) = "64"
valueSize (SignedValue v) = valueSize (UnsignedValue v)
valueSize (FloatValue (Float16Value _ )) = "16"
valueSize (FloatValue (Float32Value _ )) = "32"
valueSize (FloatValue (Float64Value _ )) = "32"

-- Parsing
p_formatstring =
  between '"' '"' $ many $ choice [
    p_stringpart <&> StringPart,
    between '{' '}' choice [
      p_exp <* char ':' <*> p_format <&> FormatExp,
      p_exp <&> FormatDefault
    ]
  ]

p_exp = (many (noneOf [char ':']))

p_format = choice [
  FormatArray <$> p_prefix <*> single <*> string ".." <*> p_format <*> p_sep <*> string ".." <*> single <*> p_suffix,
  FormatValue <$> p_prefix <*> p_ftype <*> p_suffix
]

p_sep = many $ single <* notFollowedBy $ char '.'

p_prefix =
  choice [
    char '#' $> True,
    return False :: Parser Bool
  ]
p_ftype =
  choice [
    char 'x' $> FormatHex,
    char 'X' $> FormatHeX,
    char 'b' $> FormatBin,
    char 's' $> FormatStr,
    char 'd' $> FormatDec
  ]
p_suffix = 
  choice [
    char '$' $> True,
    return False :: Parser Bool
  ]
p_stringpart = many $
  choice [
    noneOf [char '{', char '}', eof],
    string "{{" $> '{',
    string "}}" $> '}'
  ]

printCommand :: Command
printCommand =
  genCommand parseExp T.checkExp $ \(tparams, e) -> do
    if null tparams then do
      (imports, src, tenv, ienv) <- getIt
      r <- runInterpreter $ I.interpretExp ienv e
      
      else
        liftIO $ putStrLn "Cannot print declaration."

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
