{-# LANGUAGE FlexibleContexts #-}
-- | This module provides facilities for transforming L0 programs such
-- that names are unique, via the 'renameProg' function.
-- Additionally, the module also supports adding integral \"tags\" to
-- names (incarnated as the 'ID' type), in order to support more
-- efficient comparisons and renamings.  This is done by 'tagProg'.
-- The intent is that you call 'tagProg' once at some early stage,
-- then use 'renameProg' from then on.  Functions are also provided
-- for removing the tags again from expressions, patterns and typs.
module L0C.Renamer
  ( renameProg
  , tagProg
  , tagProg'
  , untagProg
  , untagExp
  , untagPattern
  , untagType
  )
  where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader

import qualified Data.Map as M
import qualified Data.Set as S

import L0C.L0
import L0C.FreshNames

-- | Rename variables such that each is unique.  The semantics of the
-- program are unaffected, under the assumption that the program was
-- correct to begin with.  In particular, the renaming may make an
-- invalid program valid.
renameProg :: (TypeBox ty, VarName vn) =>
              ProgBase ty vn -> ProgBase ty vn
renameProg prog = Prog $ runReader (evalStateT f src) env
  where env = RenameEnv M.empty newName
        src = newNameSourceForProg prog
        f = mapM renameFun $ progFunctions prog

-- | Associate a unique integer with each name in the program, taking
-- binding into account, such that the resulting 'VName's are unique.
-- The semantics of the program are unaffected, under the assumption
-- that the program was correct to begin with.
tagProg :: (TypeBox ty, VarName vn) =>
           ProgBase ty vn -> ProgBase ty (ID vn)
tagProg prog = Prog $ runReader (evalStateT f blankNameSource) env
  where env = RenameEnv M.empty newID
        f = mapM renameFun $ progFunctions prog

-- | As 'tagProg', but also return the final state of the name
-- generator.
tagProg' :: (TypeBox ty, VarName vn) =>
            ProgBase ty vn -> (ProgBase ty (ID vn), NameSource (ID vn))
tagProg' prog = let (funs, src) = runReader (runStateT f blankNameSource) env
                in (Prog funs, src)
  where env = RenameEnv M.empty newID
        f = mapM renameFun $ progFunctions prog

-- | Remove tags from a program.  Note that this is potentially
-- semantics-changing if the underlying names are not each unique.
untagProg :: (TypeBox ty, VarName vn) =>
             ProgBase ty (ID vn) -> ProgBase ty vn
untagProg = untagger $ liftM Prog . mapM renameFun . progFunctions

-- | Remove tags from an expression.  The same caveats as with
-- 'untagProg' apply.
untagExp :: (TypeBox ty, VarName vn) =>
            ExpBase ty (ID vn) -> ExpBase ty vn
untagExp = untagger renameExp

-- | Remove tags from a pattern.  The same caveats as with 'untagProg'
-- apply.
untagPattern :: (TypeBox ty, VarName vn) =>
                TupIdentBase ty (ID vn) -> TupIdentBase ty vn
untagPattern = untagger renamePattern

-- | Remove tags from a type.  The same caveats as with 'untagProg'
-- apply.
untagType :: (TypeBox (TypeBase als), VarName vn) =>
             TypeBase als (ID vn) -> TypeBase als vn
untagType = untagger renameType

untagger :: VarName vn =>
            (t -> RenameM (ID vn) vn a) -> t -> a
untagger f x = runReader (evalStateT (f x) blankNameSource) env
  where env = RenameEnv M.empty rmTag
        rmTag (ID (s, _)) src = (s, src)

data RenameEnv f t = RenameEnv {
    envNameMap :: M.Map f t
  , envNameFn  :: f -> NameSource t -> (t, NameSource t)
  }

type RenameM f t = StateT (NameSource t) (Reader (RenameEnv f t))

-- | Return a fresh, unique name.  The @Name@ is prepended to the
-- name.
new :: f -> RenameM f t t
new k = do (k', src') <- asks envNameFn <*> pure k <*> get
           put src'
           return k'

-- | 'repl s' returns the new name of the variable 's'.
repl :: (TypeBox ty, VarName f, VarName t) =>
        IdentBase ty f -> RenameM f t (IdentBase ty t)
repl (Ident name tp loc) = do
  name' <- replName name
  tp' <- renameType tp
  return $ Ident name' tp' loc

replName :: (VarName f, VarName t) => f -> RenameM f t t
replName name = maybe (new name) return =<<
                asks (M.lookup name . envNameMap)

bind :: (TypeBox ty, VarName f) => [IdentBase ty f] -> RenameM f t a -> RenameM f t a
bind vars body = do
  vars' <- mapM new varnames
  -- This works because Data.Map.union prefers elements from left
  -- operand.
  local (bind' vars') body
  where varnames = map identName vars
        bind' vars' env = env { envNameMap = M.fromList (zip varnames vars')
                                             `M.union` envNameMap env }

renameFun :: (TypeBox ty, VarName f, VarName t) =>
             FunDecBase ty f -> RenameM f t (FunDecBase ty t)
renameFun (fname, ret, params, body, pos) =
  bind params $ do
    params' <- mapM repl params
    body' <- renameExp body
    ret' <- renameType ret
    return (fname, ret', params', body', pos)

renameExp :: (TypeBox ty, VarName f, VarName t) =>
             ExpBase ty f -> RenameM f t (ExpBase ty t)
renameExp (LetWith dest src idxs ve body pos) = do
  src' <- repl src
  idxs' <- mapM renameExp idxs
  ve' <- renameExp ve
  bind [dest] $ do
    dest' <- repl dest
    body' <- renameExp body
    return (LetWith dest' src' idxs' ve' body' pos)
renameExp (LetPat pat e body pos) = do
  e1' <- renameExp e
  bind (patternNames pat) $ do
    pat' <- renamePattern pat
    body' <- renameExp body
    return $ LetPat pat' e1' body' pos
renameExp (Index s idxs t pos) = do
  s' <- repl s
  idxs' <- mapM renameExp idxs
  t' <- renameType t
  return $ Index s' idxs' t' pos
renameExp (DoLoop mergepat mergeexp loopvar e loopbody letbody pos) = do
  e' <- renameExp e
  mergeexp' <- renameExp mergeexp
  bind (patternNames mergepat) $ do
    mergepat' <- renamePattern mergepat
    letbody' <- renameExp letbody
    bind [loopvar] $ do
      loopvar'  <- repl loopvar
      loopbody' <- renameExp loopbody
      return $ DoLoop mergepat' mergeexp' loopvar' e' loopbody' letbody' pos
renameExp e = mapExpM rename e

renameType :: (TypeBox ty, VarName f, VarName t) => ty f -> RenameM f t (ty t)
renameType = mapType renameType'
  where renameType' (Array et dims u als) = do
          als' <- S.fromList <$> mapM replName (S.toList als)
          et' <- toElemDecl <$> renameElemType (fromElemDecl et)
          return $ Array et' (replicate (length dims) Nothing) u als'
        renameType' (Elem et) = Elem <$> renameElemType et
        renameElemType (Tuple ts) = Tuple <$> mapM renameType' ts
        renameElemType Int = return Int
        renameElemType Char = return Char
        renameElemType Bool = return Bool
        renameElemType Real = return Real


rename :: (TypeBox ty, VarName f, VarName t) => MapperBase ty ty f t (RenameM f t)
rename = Mapper {
           mapOnExp = renameExp
         , mapOnPattern = renamePattern
         , mapOnIdent = repl
         , mapOnLambda = renameLambda
         , mapOnType = renameType
         , mapOnValue = return
         }

renameLambda :: (TypeBox ty, VarName f, VarName t) =>
                LambdaBase ty f -> RenameM f t (LambdaBase ty t)
renameLambda (AnonymFun params body ret pos) =
  bind params $ do
    params' <- mapM repl params
    body' <- renameExp body
    ret' <- renameType ret
    return (AnonymFun params' body' ret' pos)
renameLambda (CurryFun fname curryargs rettype pos) = do
  curryargexps <- mapM (renameExp . fst) curryargs
  rettype' <- renameType rettype
  return (CurryFun fname (zip curryargexps $ map snd curryargs) rettype' pos)

renamePattern :: (TypeBox ty, VarName f, VarName t) =>
                 TupIdentBase ty f -> RenameM f t (TupIdentBase ty t)
renamePattern (Id ident) = do
  ident' <- repl ident
  return $ Id ident'
renamePattern (TupId pats pos) = do
  pats' <- mapM renamePattern pats
  return $ TupId pats' pos
renamePattern (Wildcard t loc) = do
  t' <- renameType t
  return $ Wildcard t' loc

patternNames :: TupIdentBase ty f -> [IdentBase ty f]
patternNames (Id ident)     = [ident]
patternNames (TupId pats _) = concatMap patternNames pats
patternNames (Wildcard _ _)   = []
