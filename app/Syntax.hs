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

import Data.Char (isSpace)

{-
It is probably easier to have a subtyping system,
where T (unattributed) corresponds to T@<w,w>.

This leads to the question of what (T@<w,w>)@<0,0> means.
-}

data Ident
    = Unqualified String
    | Qualified String String
    | Gen Int
    | Hole
    deriving(Eq,Ord)

instance Show Ident where
    show (Unqualified s) = s
    show (Qualified m s) = m ++ "." ++ s
    show (Gen i) = "v_" ++ show i
    show Hole = "_"

data Sign
    = SZero
    | SPos
    deriving(Eq)

data Affine
    = Zero
    | Linear
    | Affine
    | Omega
    deriving(Eq)

instance Show Affine where
    show Zero = "0"
    show Linear = "1"
    show Affine = "?"
    show Omega = "!"

data Usage
    = Usage
    { erased :: Affine
    , runtime :: Affine
    } deriving(Eq)

instance Show Usage where
    show (Usage Omega Omega) = "!"
    show (Usage Omega Linear) = "*"
    show (Usage Linear Zero) = "~"
    show (Usage Omega Affine) = "?"
    show (Usage Omega Zero) = "@"
    show (Usage a b) = "<" ++ show a ++ "," ++ show b ++ ">"

class PartialOrd t where
    pleq :: t -> t -> Bool
    pzero :: t
    meet :: t -> t -> t

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
    _ `pleq` Omega = True
    Linear `pleq` Affine = True
    Zero `pleq` Affine = True
    _ `pleq` _ = False

    pzero = Zero

    meet Zero x = x
    meet x Zero = x
    meet x y | x `pleq` y = x
    meet y x | y `pleq` x = y

instance Semiring Affine Sign where
    szero = SZero
    
    radd Zero x = x
    radd x Zero  = x
    radd _ _ = Omega

    rsign Zero = SZero
    rsign _ = SPos

    rmul SZero _ = rzero
    rmul SPos x = x

instance PartialOrd Usage where
    Usage x y `pleq` Usage v w = x `pleq` v && y `pleq` w

    pzero = Usage pzero pzero

    meet (Usage x y) (Usage v w) = Usage (meet x v) (meet y w)

instance Semiring Usage (Sign,Sign) where
    szero = (SZero,SZero)

    radd (Usage x y) (Usage v w) = Usage (radd x v) (radd y w)

    rsign (Usage x y) = (rsign x,rsign y)
    rmul (a,b) (Usage x y) = Usage (rmul a x) (rmul b y)

{-
ideally:

- {T :: <!,0>Type, <!,n>T} should be able to be used <!,n> times.
- (T :: <!,0>Type) -> <!,n>T -> <!,n>T (where T is free in the body)
    should be able to be used <!,n> times.

This is important for the admissibility of substitution:
- (\(T :: <!,0>Type) (x :: !T) -> id T x) has fvs T and x in the body, but
    should still be able to be used !-many times, as T has runtime usage 0.
    Otherwise, substituting id leads to a term with a different usage.

And so we have the following subusaging rules:
- anything can be subusaged as a 0
- if a given term has free variables a, then the term has usage min{usage(a)},
    where min{x} is the lowest non-zero usage in x.
-}

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
    deriving(Eq)

makeBaseFunctor ''Expr

toTerm :: String -> String
toTerm xs | any isSpace xs = "(" ++ xs ++ ")"
toTerm xs = xs

instance Show Expr where
    show = cata go
        where
            go (AttrF e u) = show u ++ toTerm e
            go TypeF = "Type"
            go TopF = "Top"
            go UnitF = "Unit"
            go (ProdF Hole t s) = toTerm t ++ " -> " ++ s
            go (ProdF n t s) = "(" ++ show n ++ " :: " ++ t ++ ") -> " ++ s
            go (SumF n t s) = "{" ++ show n ++ " :: " ++ t ++ "," ++ s ++ "}"
            go (VarF n) = show n
            go (PairF a b) = "(" ++ a ++ "," ++ b ++ ")"
            go (AbsF n e) = "(\\" ++ show n ++ " -> " ++ e ++ ")"
            go (UnpairF vs p b) = "let " ++ show vs ++ " = " ++ " in " ++ b
            go (AppF f x) = f ++ " " ++ toTerm x
            go (AnnF e t) = "(" ++ e ++ " :: " ++ t ++ ")"

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