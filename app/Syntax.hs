{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Syntax where

import qualified Data.Map as M

import Data.Functor.Foldable
import Data.Functor.Foldable.TH

{-
It is probably easier to have a subtyping system,
where T (unattributed) corresponds to T@<w,w>.

This leads to the question of what (T@<w,w>)@<0,0> means.
-}

data Ident
    = Unqualified String
    | Qualified String String
    | Gen Int
    deriving(Eq,Ord,Show)

data Sign
    = Zero
    | Positive
    deriving(Eq)

data Affine
    = Linear Int
    | Affine Int
    | Omega
    deriving(Eq,Show)

data Usage
    = Usage
    { erased :: Affine
    , runtime :: Affine
    } deriving(Eq,Show)

class PartialOrd t where
    pleq :: t -> t -> Bool
    pzero :: t
    meet :: t -> t -> t
    meet x y | x `pleq` y = x
    meet x y | y `pleq` x = y
    meet _ _ = pzero

class (PartialOrd t, Eq s) => Semiring t s | t -> s where
    rzero :: t
    rzero = pzero
    szero :: s

    radd :: t -> t -> t

    rsign :: t -> s

    rmul :: s -> t -> t

    rleq :: t -> t -> Bool
    rleq = pleq

instance PartialOrd Affine where
    -- here a <= b means 'a can be used in place of b' or 'a value of b can be used as an a'
    x `pleq` y | x == y = True
    Linear 0 `pleq` _ = True
    _ `pleq` Omega = True
    Affine a `pleq` Affine b = a <= b
    Linear a `pleq` Affine b = a <= b
    _ `pleq` _ = False

    pzero = Linear 0

instance Semiring Affine Sign where
    szero = Zero
    
    radd (Linear 0) x = x
    radd x (Linear 0) = x
    radd (Linear x) (Linear y) = Linear (x + y)
    radd (Affine x) (Affine y) = Affine (x + y)
    radd (Linear x) (Affine y) = Affine (x + y)
    radd (Affine x) (Linear y) = Affine (x + y)
    radd Omega _ = Omega
    radd _ Omega = Omega

    rsign (Linear 0) = Zero
    rsign _ = Positive

    rmul Zero _ = rzero
    rmul Positive x = x

instance PartialOrd Usage where
    Usage x y `pleq` Usage v w = x `pleq` v && y `pleq` w

    pzero = Usage pzero pzero

instance Semiring Usage (Sign,Sign) where
    szero = (Zero,Zero)

    radd (Usage x y) (Usage v w) = Usage (radd x v) (radd y w)

    rsign (Usage x y) = (rsign x,rsign y)
    rmul (a,b) (Usage x y) = Usage (rmul a x) (rmul b y)

data Expr
    = Attr Expr Usage
    | Type
    | Top
    | Unit
    | Prod Ident Expr Expr
    | Sum Ident Expr Expr
    | Var Ident
    | Pair Expr Expr
    | Abs Ident Expr
    | Unpair (Ident,Ident) Expr Expr
    | App Expr Expr
    | Ann Expr Expr
    deriving(Show,Eq)

makeBaseFunctor ''Expr

type Type = Expr

newtype Env = Env (M.Map Ident (Type,Usage))
newtype UsageEnv = UsageEnv (M.Map Ident Usage)

deleteU :: Ident -> UsageEnv -> UsageEnv
deleteU i (UsageEnv m) = UsageEnv (M.delete i m)

lookupU :: Ident -> UsageEnv -> Maybe Usage
lookupU i (UsageEnv m) = M.lookup i m

singletonU :: Ident -> Usage -> UsageEnv
singletonU i u = UsageEnv (M.singleton i u)

class Semiring r s => SemiringModule m r s | m -> r, r -> s where
    madd :: m -> m -> m
    mmul :: s -> m -> m

instance SemiringModule UsageEnv Usage (Sign,Sign) where
    mmul s (UsageEnv m) = UsageEnv (fmap (rmul s) m)
    madd (UsageEnv m) (UsageEnv n) = UsageEnv (M.fromSet
        (\i -> radd (M.findWithDefault rzero i m) (M.findWithDefault rzero i n)) (M.keysSet m <> M.keysSet n))

instance Semigroup UsageEnv where
    (<>) = madd

instance Monoid UsageEnv where
    mempty = UsageEnv M.empty

newtype Subst = Subst (M.Map Ident Expr)

subst :: Subst -> Expr -> Expr
subst (Subst g) = cata go
    where
        go (VarF i) = case M.lookup i g of
            Just e -> e
            Nothing -> Var i
        go x = embed x