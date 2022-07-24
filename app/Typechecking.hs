{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
module Typechecking where

import qualified Data.Map as M
import qualified Data.Set as S

import Data.Functor.Foldable

import Syntax

import Control.Monad
import Control.Monad.RWS (RWST, runRWST, listen, listens, pass, tell, get, asks, put, local)
import Control.Monad.Except

data TypeError
    = NotSynthesizable Expr
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
typeUsage = Usage Omega (Linear 0)

unrestricted :: Usage
unrestricted = Usage Omega Omega

type UsageCtx = (Sign,Sign)

type Checker = RWST (UsageCtx,Usage,Env) UsageEnv Int (Except TypeError)

enterCtx :: UsageCtx -> Checker a -> Checker a
enterCtx c = local (\(_,u,g)->(c,u,g))

requireN :: Usage -> Checker a -> Checker a
requireN u = local (\(c,_,g)->(c,u,g))

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
        (x,y) -> throwError (NotSubtype x y)

withVar :: Ident -> (Type,Usage) -> Checker a -> Checker a
withVar i (t,l) f = pass $ do
    (a,m) <- listen (local (\(c,u,Env g)->(c,u,Env (M.insert i (t,l) g))) f)
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

lookupVar :: Ident -> Checker ((Type,Usage),Usage)
lookupVar v = do
    (c,u,r) <- asks (\(c,u,Env g) -> (c,u,M.lookup v g))
    case r of
        Just r -> pure (r,u)
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
check (Abs i e) (Prod j tb sb,u) = do
    (t,u0) <- destructType tb
    (s,u1) <- destructType sb
    let s' = subst (Subst (M.singleton j (Var i))) s
    (_,u2) <- minFree (withVar i (t,u0) (requireN u1 (check e (s',u1))))
    subusage u u2
check (Pair x y) (Sum j tb sb,u) = do
    (t,u0) <- destructType tb
    (s,u1) <- destructType sb
    (_,u2) <- minFree (requireN u0 (check x (t,u0)))
    x' <- renameBound x
    let s' = subst (Subst (M.singleton j x')) s
    (_,u3) <- minFree (requireN u1 (check y (s',u1)))
    subusage u u2
    subusage u u3
check x (Attr y u,u') = do
    check x (y,u)
    subusage u' u
check x (y,u) = do
    x' <- whnf x
    y' <- whnf y
    case (x',y') of
        (Just x',Nothing) -> check x' (y,u)
        (Nothing,Just y') -> check x (y',u)
        (Just x',Just y') -> check x' (y',u)
        (Nothing,Nothing) -> do
            (t,u') <- synthesize x
            subtype y t
            subusage u u'

synthesize :: Expr -> Checker (Type,Usage)
synthesize Top = pure (Type,typeUsage)
synthesize Type = pure (Type,typeUsage)
synthesize Unit = pure (Top,unrestricted)
synthesize (Attr t u) = do
    check t (Type,typeUsage)
    pure (Type,typeUsage)
synthesize (Ann e tb) = do
    enterCtx (szero @Usage :: UsageCtx) (check tb (Type,typeUsage))
    (t,u) <- destructType tb
    check e (t,u)
    pure (t,u)
synthesize (Prod i tb sb) = enterCtx (szero @Usage :: UsageCtx) $ do
    check tb (Type,typeUsage)
    (t,_) <- destructType tb
    withVar i (t,unrestricted) (check sb (Type,typeUsage))
    pure (Type,typeUsage)
synthesize (Sum i tb sb) = enterCtx (szero @Usage :: UsageCtx) $ do
    check tb (Type,typeUsage)
    (t,_) <- destructType tb
    withVar i (t,unrestricted) (check sb (Type,typeUsage))
    pure (Type,Usage Omega rzero)
synthesize (App f x) = do
    (t,_) <- synthesize f
    t' <- toWhnf t
    case t' of
        Prod i tb sb -> do
            (t,u0) <- destructType tb
            (s,u1) <- destructType sb
            requireN u0 (check x (t,u0))
            x' <- renameBound x
            pure (subst (Subst (M.singleton i x')) s,u1)
        _ -> throwError (NonFunctionApp f)
synthesize (Unpair (x,y) p e) = do
    (t,_) <- synthesize p
    t' <- toWhnf t
    case t' of
        Sum i tb sb -> do
            (t,u0) <- destructType tb
            (s,u1) <- destructType sb
            let s' = subst (Subst (M.singleton i (Var x))) s
            withVar x (t,u0) (withVar y (s',u1) (synthesize e))
        _ -> throwError (NonPairDestruct p)
synthesize (Var v) = do
    ((t,u),r) <- lookupVar v
    tell (UsageEnv (M.singleton v u))
    pure (t,r)
synthesize x = throwError (NotSynthesizable x)

typecheck :: Expr -> (UsageCtx,Usage,Env) -> Int -> Either TypeError ((Type,Usage),Int,UsageEnv)
typecheck e r s = runExcept (runRWST (synthesize e) r s)