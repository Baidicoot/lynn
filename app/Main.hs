module Main where

import Typechecking
import Syntax
import Parser

import Control.Monad
import qualified Data.Map as M

-- ((\T p -> (p,Unit)) :: <<w,0> T :: Type> -> <<0,1> p :: T> -> {<0,1> p :: T, Top})

evalTL :: TL -> (Env,Defs) -> IO (Env,Defs)
evalTL (Assert u n t) (Env e,Defs d) = case runCheck t (Type,u) (Env e,Defs d) 0 of
    Right _ -> putStrLn (show u ++ " " ++ show n ++ " : " ++ show t) >> pure (Env (M.insert n (t,u) e),Defs d)
    Left err -> print err >> pure (Env e,Defs d)
evalTL (Define u n b) (Env e,Defs d) = case runSynthesize b u (Env e,Defs d) 0 of
    Right (t,_,_) -> putStrLn (show u ++ " " ++ show n ++ " : " ++ show t) >> pure (Env (M.insert n (t,u) e),Defs (M.insert n b d))
    Left err -> print err >> pure (Env e,Defs d)
evalTL (Eval u b) (e,d) = case runWhnf b u (e,d) 0 of
    Right ((b,t),_,_) -> putStrLn (show u ++ " " ++ show b ++ " : " ++ show t) >> pure (e,d)
    Left err -> print err >> pure (e,d)

mainloop :: (Env,Defs) -> IO ()
mainloop g = do
    l <- getLine
    g' <- case parseTL "" l of
        Right t -> evalTL t g
        Left e -> putStr "parseerror: " >> print e >> pure g
    mainloop g'

main :: IO ()
main = mainloop (Env M.empty,Defs M.empty)