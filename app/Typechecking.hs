{-# LANGUAGE TypeFamilies #-}
module Typechecking where

import qualified Data.Map as M
import qualified Data.Set as S

import Data.Functor.Foldable

import Syntax

import Control.Monad
import Control.Monad.RWS (RWST, runRWST, listen, pass, tell, get, asks, put, local)
import Control.Monad.Except

data TypeError
    = NotSynthesizable Expr
    | NotSubtype Expr Expr
    | NotSublin Usage Usage
    | NonFunctionApp Expr
    | NonPairDestruct Expr
    | WrongUsage Ident Usage Usage
    | UnknownVar Ident
    deriving(Show)

data UsageCtx
    = Annot
    | Term

toMul :: UsageCtx -> Usage
toMul Annot = rzero
toMul Term = rone

toUsage :: UsageCtx -> Usage
toUsage Annot = rzero
toUsage Term = rone

type Checker = RWST (UsageCtx,Env) UsageEnv Int (Except TypeError)

mulUsage :: Usage -> Checker a -> Checker a
mulUsage u f = pass $ do
    a <- f
    pure (a,mmul u)

withCtx :: UsageCtx -> Checker a -> Checker a
withCtx u = local (\(_,e)->(u,e))

enterCtx :: UsageCtx -> Checker a -> Checker a
enterCtx u = mulUsage (toMul u) . withCtx u 

renameBound :: Expr -> Checker Expr
renameBound e = cata go e M.empty
    where
        go :: ExprF (M.Map Ident Ident -> Checker Expr) -> M.Map Ident Ident -> Checker Expr
        go (ProdF (i,l) t s) g = do
            t' <- t g
            j <- fresh
            s' <- s (M.insert i j g)
            pure (Prod (j,l) t' s')
        go (SumF (i,l) t s) g = do
            t' <- t g
            j <- fresh
            s' <- s (M.insert i j g)
            pure (Sum (j,l) t' s')
        go (AbsF i e) g = do
            j <- fresh
            e' <- e (M.insert i j g)
            pure (Abs j e')
        go (VarF i) g = pure (Var (M.findWithDefault i i g))
        go x g = fmap embed (sequence (sequence x g))

whnf :: Expr -> Checker (Maybe Expr)
whnf (App f e) = do
    f' <- whnf f
    case f' of
        Just (Abs i b) -> do
            e' <- renameBound e
            whnf (subst (Subst (M.singleton i e')) b)
        _ -> pure Nothing
whnf (Destruct (x,y) p e) = do
    p' <- whnf p
    case p' of
        Just (Pair xe ye) -> do
            xe' <- renameBound xe
            ye' <- renameBound ye
            whnf (subst (Subst (M.fromList [(x,xe'),(y,ye')])) e)
        _ -> pure Nothing
whnf x = pure Nothing

toWhnf :: Expr -> Checker Expr
toWhnf e = do
    e' <- whnf e
    case e' of
        Just e' -> pure e'
        Nothing -> pure e

sublin :: Usage -> Usage -> Checker ()
sublin x y =
    if x `rleq` y then
        pure ()
    else
        throwError (NotSublin x y)

-- subtype checking between normalized terms
subtype :: Expr -> Expr -> Checker ()
subtype a b = do
    a <- toWhnf a
    b <- toWhnf b
    case (a,b) of
        (Prod (i,l0) t0 s0,Prod (j,l1) t1 s1) -> do
            sublin l0 l1
            subtype t0 t1
            subtype s0 (subst (Subst (M.singleton j (Var i))) s1)
        (Sum (i,l0) t0 s0,Sum (j,l1) t1 s1) -> do
            sublin l0 l1
            subtype t0 t1
            subtype s0 (subst (Subst (M.singleton j (Var i))) s1)
        (Abs i e0,Abs j e1) -> subtype e0 (subst (Subst (M.singleton j (Var i))) e1)
        (Pair x0 y0,Pair x1 y1) -> do
            subtype x0 x1
            subtype y0 y1
        (App f0 e0,App f1 e1) -> do
            subtype f0 f1
            subtype e0 e1
        (Destruct (x0,y0) p0 e0,Destruct (x1,y1) p1 e1) -> do
            subtype p0 p1
            subtype e0 (subst (Subst (M.fromList [(x1,Var x0),(y1,Var y1)])) e1)
        (Ann e0 t0,Ann e1 t1) -> do
            subtype t0 t1
            subtype e0 e1
        (x,y) | x == y -> pure ()

withVar :: Ident -> (Expr,Usage) -> Checker a -> Checker a
withVar i (t,l) f = pass $ do
    (a,m) <- listen (local (\(u,Env g) -> (u,Env (M.insert i t g))) f)
    let u = case lookupU i m of
            Just u -> u
            Nothing -> rzero
    if u `rleq` l then
        pure (a,deleteU i)
    else
        throwError (WrongUsage i l u)

fresh :: Checker Ident
fresh = do
    i <- get
    put (i+1)
    pure (Gen i)

lookupVar :: Ident -> Checker Expr
lookupVar v = do
    r <- asks (\(_,Env g) -> M.lookup v g)
    case r of
        Just r -> pure r
        Nothing -> throwError (UnknownVar v)

check :: Expr -> Expr -> Checker ()
check (Abs i e) (Prod (j,l) t s) = do
    let s' = subst (Subst (M.singleton j (Var i))) s
    withVar i (t,l) (check e s')
check (Pair x y) (Sum (j,l) t s) = do
    s' <- flip (subst . Subst . M.singleton j) s <$> renameBound x
    check x t
    check y s'
check x y = do
    x' <- whnf x
    y' <- whnf y
    case (x',y') of
        (Just x',Nothing) -> check x' y
        (Nothing,Just y') -> check x y'
        (Just x',Just y') -> check x' y'
        (Nothing,Nothing) -> do
            t <- synthesize x
            subtype t y

synthesize :: Expr -> Checker Expr
synthesize Top = pure Type
synthesize Unit = pure Top
synthesize Type = pure Type
synthesize (App f x) = do
    ft <- whnf =<< synthesize f
    case ft of
        Just (Prod (i,l) t s) -> do
            mulUsage l (check x t)
            pure (subst (Subst (M.singleton i x)) s)
        Nothing -> throwError (NonFunctionApp f)
synthesize (Destruct (x,y) p e) = do
    pt <- whnf =<< synthesize p
    case pt of
        Just (Sum (i,l) t s) -> do
            let s' = subst (Subst (M.singleton i (Var x))) s
            withVar x (t,l) (withVar y (s',Usage Omega Omega) (synthesize e))
        Nothing -> throwError (NonPairDestruct p)
synthesize (Prod (i,_) t s) = enterCtx Annot $ do
    check t Type
    withVar i (t,rzero) (check s Type)
    pure Type
synthesize (Sum (i,_) t s) = enterCtx Annot $ do
    check t Type
    withVar i (t,rzero) (check s Type)
    pure Type
synthesize (Var v) = do
    u <- asks fst
    tell (singletonU v (toUsage u))
    lookupVar v
synthesize (Ann e t) = do
    enterCtx Annot (check t Type)
    check e t
    pure t
synthesize x = throwError (NotSynthesizable x)

typecheck :: (UsageCtx,Env) -> Int -> Expr -> Either TypeError Expr
typecheck r s e = fmap (\(t,_,_)->t) (runExcept (runRWST (synthesize e) r s))