module Main where

import Typechecking
import Syntax
import Parser

import Control.Monad
import qualified Data.Map as M

-- ((\T p -> (p,Unit)) :: <<w,0> T :: Type> -> <<0,1> p :: T> -> {<0,1> p :: T, Top})

main :: IO ()
main = do
    l <- getLine
    case parseTL "" l of
        Right e ->
            case typecheck (Term,Env M.empty) 0 e of
                Right t -> print t
                Left e -> putStr "typeerror: " >> print e
        Left e -> putStr "parseerror: " >> print e
    main