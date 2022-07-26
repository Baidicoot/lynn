{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
module Typechecking where

import qualified Data.Map as M
import qualified Data.Set as S

import Data.Functor.Foldable

import Syntax

import Control.Monad
import Control.Monad.RWS (RWST, runRWST, listen, listens, pass, tell, get, ask, asks, put, local)
import Control.Monad.Except

data TypeError
    = Debug String TypeError
    | WhileUnify Expr Expr TypeError
    | WhileCheck Expr (Type,Usage) TypeError
    | NotSynthesizable Expr
    | NotSubtype Expr Expr
    | NotSubusage Usage Usage
    | NonFunctionApp Expr
    | NonPairDestruct Expr
    | NotBaseType Expr
    | NotType Expr
    | WrongUsage Ident Usage Usage
    | UnknownVar Ident
    deriving(Show)

typeUsage :: Usage
typeUsage = Usage Omega Zero

unrestricted :: Usage
unrestricted = Usage Omega Omega

type UsageCtx = (Sign,Sign)

newtype Defs = Defs (M.Map Ident Expr)

type Checker = RWST (Env,Defs) UsageEnv Int (Except TypeError)

destructType :: Type -> Checker (Type,Usage)
destructType = go <=< toWhnf
    where
        go :: Type -> Checker (Type,Usage)
        go (Attr t u) = pure (t,u)
        go t = pure (t,unrestricted)

renameBound :: Expr -> Checker Expr
renameBound e = cata go e M.empty
    where
        go :: ExprF (M.Map Ident Ident -> Checker Expr) -> M.Map Ident Ident -> Checker Expr
        go (ProdF i t s) g = do
            t <- t g
            j <- fresh
            s' <- s (M.insert i j g)
            pure (Prod j t s')
        go (SumF i t s) g = do
            t' <- t g
            j <- fresh
            s' <- s (M.insert i j g)
            pure (Sum j t' s')
        go (AbsF i e) g = do
            j <- fresh
            e' <- e (M.insert i j g)
            pure (Abs j e')
        go (VarF i) g = pure (Var (M.findWithDefault i i g))
        go x g = fmap embed (sequence (sequence x g))

whnfStep :: Expr -> Checker (Maybe Expr)
whnfStep (App f e) = do
    f' <- whnf f
    case f' of
        Just (Abs i b) -> do
            e' <- renameBound e
            pure (Just (subst (Subst (M.singleton i e')) b))
        _ -> pure Nothing
whnfStep (Unpair (x,y) p e) = do
    p' <- whnf p
    case p' of
        Just (Pair xe ye) -> do
            xe' <- renameBound xe
            ye' <- renameBound ye
            pure (Just (subst (Subst (M.fromList [(x,xe'),(y,ye')])) e))
        _ -> pure Nothing
whnfStep x = pure Nothing

whnf :: Expr -> Checker (Maybe Expr)
whnf = go <=< whnfStep
    where
        go (Just e) = do
            e' <- whnfStep e
            case e' of
                Just _ -> go e'
                Nothing -> pure (Just e)
        go Nothing = pure Nothing

toWhnf :: Expr -> Checker Expr
toWhnf e = do
    e' <- whnf e
    case e' of
        Just e' -> pure e'
        Nothing -> pure e

inlineDefsHead :: Expr -> Checker (Maybe Expr)
inlineDefsHead (Var v) = do
    (_,Defs d) <- ask
    case M.lookup v d of
        Just e -> pure (Just e)
        _ -> pure Nothing
inlineDefsHead (App f x) = (fmap . fmap) (flip App x) (inlineDefsHead f)
inlineDefsHead (Unpair v p e) = (fmap . fmap) (flip (Unpair v) e) (inlineDefsHead p)
inlineDefsHead _ = pure Nothing

subusage :: Usage -> Usage -> Checker ()
subusage x y =
    if x `rleq` y then
        pure ()
    else
        throwError (NotSubusage x y)

subtype :: Expr -> Expr -> Checker ()
subtype a b = do
    a <- toWhnf a
    b <- toWhnf b
    case (a,b) of
        (Prod i t0 s0,Prod j t1 s1) -> do
            subtype t0 t1
            subtype s0 (subst (Subst (M.singleton j (Var i))) s1)
        (Sum i t0 s0,Sum j t1 s1) -> do
            subtype t0 t1
            subtype s0 (subst (Subst (M.singleton j (Var i))) s1)
        (Abs i e0,Abs j e1) -> subtype e0 (subst (Subst (M.singleton j (Var i))) e1)
        (Pair x0 y0,Pair x1 y1) -> do
            subtype x0 x1
            subtype y0 y1
        (App f0 e0,App f1 e1) -> do
            subtype f0 f1
            subtype e0 e1
        (Unpair (x0,y0) p0 e0,Unpair (x1,y1) p1 e1) -> do
            subtype p0 p1
            subtype e0 (subst (Subst (M.fromList [(x1,Var x0),(y1,Var y1)])) e1)
        (Ann e0 t0,Ann e1 t1) -> do
            subtype t0 t1
            subtype e0 e1
        (Attr e0 l0,Attr e1 l1) -> do
            subtype e0 e1
            subusage l0 l1
        (Attr e l,t) -> subtype e t
        (t,Attr e l) -> do
            subtype t e
            subusage unrestricted l
        (x,y) | x == y -> pure ()
        (x,y) -> flip catchError (throwError . WhileUnify x y) $ do
            x' <- inlineDefsHead x
            y' <- inlineDefsHead y
            case (x',y') of
                (Just x',Just y') -> subtype x' y'
                (Nothing,Just y') -> subtype x y'
                (Just x',Nothing) -> subtype x' y
                (Nothing,Nothing) -> throwError (NotSubtype x y)

withVar :: Ident -> (Type,Usage) -> Checker a -> Checker a
withVar i (t,l) f = pass $ do
    (a,m) <- listen (local (\(Env g,d)->(Env (M.insert i (t,l) g),d)) f)
    let u = case lookupU i m of
            Just u -> u
            Nothing -> rzero
    if u `rleq` l then
        pure (a,deleteU i)
    else
        throwError (WrongUsage i l u)

minFree :: Checker a -> Checker (a,Usage)
minFree = listens (\(UsageEnv m)->foldr meet unrestricted (M.elems m))

fresh :: Checker Ident
fresh = do
    i <- get
    put (i+1)
    pure (Gen i)

lookupVar :: Ident -> Checker (Type,Usage)
lookupVar v = do
    t <- asks (\(Env g,d) -> M.lookup v g)
    case t of
        Just (t,u) -> pure (t,u)
        Nothing -> throwError (UnknownVar v)

-- `check c e (b,u)` means 'check expression `e` has type `b@u` in usage context `c`'
-- `synthesize c e` means 'synthesize the type and usage of `e` in usage context `c`'

{-
typing rules for app:

Ctx0 |- s0 f : ((x : T@u1) -> S@u2)@u3
Ctx1 |- u1 x : T@u1
-------------------------------------
Ctx0 + Ctx1 |- s0 (f x) : S@u2
-}

check :: Expr -> (Type,Usage) -> Checker ()
check (Abs i e) (Prod j tb sb,r) = do
    (t,u0) <- destructType tb
    (s,u1) <- destructType sb
    let s' = subst (Subst (M.singleton j (Var i))) s
    (_,u2) <- minFree (withVar i (t,u0) (check e (s',u1)))
    subusage r u2
check (Pair x y) (Sum j tb sb,r) = do
    (t,u0) <- destructType tb
    (_,u1) <- minFree (check x (t,u0))
    subusage u0 u1
    x' <- renameBound x
    let sb' = subst (Subst (M.singleton j x')) sb
    (s,u2) <- destructType sb'
    (_,u3) <- minFree (check y (s,u2))
    subusage u2 u3
    subusage r (meet u0 u2)
check x (Attr y u,r) = do
    check x (y,u)
    subusage r u
check x (y,r) = do
    x' <- whnf x
    y' <- whnf y
    case (x',y') of
        (Just x',Nothing) -> check x' (y,r)
        (Nothing,Just y') -> check x (y',r)
        (Just x',Just y') -> check x' (y',r)
        (Nothing,Nothing) -> do
            t <- synthesize x r
            subtype y t

synthesize :: Expr -> Usage -> Checker Type
synthesize Top r = pure Type
synthesize Type r = pure Type
synthesize Unit r = pure Top
synthesize (Attr t a) r = do
    check t (Type,typeUsage)
    pure Type
synthesize (Ann e tb) r = do
    check tb (Type,rzero)
    (t,u) <- destructType tb
    check e (t,u)
    subusage r u
    pure t
synthesize (Prod i tb sb) r = do
    check tb (Type,rzero)
    (t,_) <- destructType tb
    withVar i (t,unrestricted) (check sb (Type,rzero))
    pure Type
synthesize (Sum i tb sb) r = do
    check tb (Type,rzero)
    (t,_) <- destructType tb
    withVar i (t,unrestricted) (check sb (Type,rzero))
    pure Type
synthesize (App f x) r = do
    t <- toWhnf =<< synthesize f r
    case t of
        Prod i tb sb -> do
            (t,u0) <- destructType tb
            (s,u1) <- destructType sb
            check x (t,u0)
            x' <- renameBound x
            pure (subst (Subst (M.singleton i x')) s)
        _ -> throwError (NonFunctionApp f)
synthesize (Unpair (x,y) p e) r = do
    t <- toWhnf =<< synthesize p r
    case t of
        Sum i tb sb -> do
            (t,u0) <- destructType tb
            (s,u1) <- destructType sb
            let s' = subst (Subst (M.singleton i (Var x))) s
            withVar x (t,u0) (withVar y (s',u1) (synthesize e r))
        _ -> throwError (NonPairDestruct p)
synthesize (Var v) r = do
    (t,u) <- lookupVar v
    subusage r u
    tell (UsageEnv (M.singleton v r))
    pure t
synthesize x r = throwError (NotSynthesizable x)

runSynthesize :: Expr -> Usage -> (Env,Defs) -> Int -> Either TypeError (Type,Int,UsageEnv)
runSynthesize e u r s = runExcept (runRWST (synthesize e u) r s)

runCheck :: Expr -> (Type,Usage) -> (Env,Defs) -> Int -> Either TypeError ((),Int,UsageEnv)
runCheck e t r s = runExcept (runRWST (check e t) r s)

runWhnf :: Expr -> Usage -> (Env,Defs) -> Int -> Either TypeError ((Expr,Type),Int,UsageEnv)
runWhnf e u r s = runExcept (runRWST (synthesize e u >>= \t -> fmap (flip (,) t) (toWhnf e)) r s)