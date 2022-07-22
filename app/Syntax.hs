{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
module Syntax where

import qualified Data.Map as M

import Data.Functor.Foldable
import Data.Functor.Foldable.TH

data Ident
    = Unqualified String
    | Qualified String String
    | Gen Int
    deriving(Eq,Ord,Show)

data Multiplicity
    = Zero
    | Succ Multiplicity
    | Omega
    deriving(Eq,Show)

class Semiring t where
    rzero :: t
    rone :: t
    radd :: t -> t -> t
    rmul :: t -> t -> t

    rleq :: t -> t -> Bool

instance Semiring Multiplicity where
    rzero = Zero

    rone = Succ Zero
    
    radd Zero x = x
    radd x Zero = x
    radd Omega _ = Omega
    radd _ Omega = Omega
    radd (Succ x) y = Succ (radd x y)

    rmul Zero _ = Zero
    rmul _ Zero = Zero
    rmul Omega _ = Omega
    rmul _ Omega = Omega
    rmul (Succ x) y = radd y (rmul x y)

    rleq Zero Zero = True
    rleq _ Omega = True
    rleq (Succ x) (Succ y) = rleq x y
    rleq _ _ = False

data Usage
    = Usage
    { erased :: Multiplicity
    , runtime :: Multiplicity
    }
    deriving(Eq,Show)

instance Semiring Usage where
    rzero = Usage rzero rzero
    rone = Usage rone rone

    radd (Usage x y) (Usage v w) = Usage (radd x v) (radd y w)

    rmul (Usage x y) (Usage v w) = Usage (rmul x v) (rmul y w)

    rleq (Usage x y) (Usage v w) = rleq x v && rleq y w

{-
QTT is insufficent for this usecase; usage annotations are needed for returned values

proposed syntax:
k :=
    | Type :: BaseType
    | BaseType :: BaseType
    | Usage :: BaseType

m :=
    | Omega
    | Zero
    | Succ m

u :=
    | (m,m) :: Usage

T :=
    | B@u :: Type

B :=
    | k
    | Top
    | (x :: T) -> T
    | {x :: T, T}

t :=
    | T
    | (t,t)
    | (\x. t)
    | let (x,y) = t in t
    | t t
-}

data Expr
    -- kinds
    = Type
    -- types
    | Sum (Ident,Usage) Expr Expr
    | Prod (Ident,Usage) Expr Expr
    | Top
    -- terms
    | Var Ident
    | App Expr Expr
    | Abs Ident Expr
    | Destruct (Ident,Ident) Expr Expr
    | Pair Expr Expr
    | Ann Expr Expr
    | Unit
    deriving(Eq,Show)

makeBaseFunctor ''Expr

type Type = Expr

newtype Env = Env (M.Map Ident Expr)
newtype UsageEnv = UsageEnv (M.Map Ident Usage)

deleteU :: Ident -> UsageEnv -> UsageEnv
deleteU i (UsageEnv m) = UsageEnv (M.delete i m)

lookupU :: Ident -> UsageEnv -> Maybe Usage
lookupU i (UsageEnv m) = M.lookup i m

singletonU :: Ident -> Usage -> UsageEnv
singletonU i u = UsageEnv (M.singleton i u)

class SemiringModule s m | m -> s where
    mmul :: s -> m -> m
    madd :: m -> m -> m

instance SemiringModule Usage UsageEnv where
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