module Parser (parseTL) where

import Syntax

import Text.Parsec
import qualified Text.Parsec.Token as Token
import Text.Parsec.Expr
import Text.Parsec.Language (haskellDef)

import Control.Monad
import Control.Monad.Identity

import Data.Char (isUpper)

import Data.Bifunctor

import qualified Data.Set as S
import Data.Either (partitionEithers)

type Parser = Parsec String ()
type Op = Operator String () Identity

data TLExpr
    = TLDec Expr Expr
    | TLDef Ident Expr

bijou :: Token.LanguageDef a
bijou = haskellDef
    { Token.reservedNames = Token.reservedNames haskellDef
        ++ ["Type", "Unit", "Top"]
        ++ ["case","of","end"]
        ++ ["do","then", "ret"]
        ++ ["dec","def"]
        ++ ["entry","extern","export"]
        ++ ["let","letrec","val","in"]
        ++ ["ccall","prim"]
        ++ ["data","gadt","struct"]
    , Token.reservedOpNames = Token.reservedOpNames haskellDef
        ++ [".",",","(->)","->"]
    }

reservedOpNames :: [String]
reservedOpNames = Token.reservedOpNames bijou

lexer :: Token.TokenParser s
lexer = Token.makeTokenParser bijou

parens :: Parser a -> Parser a
parens = Token.parens lexer

braces :: Parser a -> Parser a
braces = Token.braces lexer

angles :: Parser a -> Parser a
angles = Token.angles lexer

identifier :: Parser String
identifier = Token.identifier lexer

reserved :: String -> Parser ()
reserved = Token.reserved lexer

lexeme :: Parser a -> Parser a
lexeme = Token.lexeme lexer

unlexIdent :: Parser String
unlexIdent = (do
    c <- Token.identStart bijou
    cs <- many (Token.identLetter bijou)
    pure (c:cs))
    <?> "identifier"

qualifiedName :: Parser Ident
qualifiedName = lexeme . try $ do
    m <- unlexIdent
    char '.'
    fmap (Qualified m) unlexIdent

name :: Parser Ident
name = 
    qualifiedName
    <|> fmap Unqualified identifier

weakName :: Parser Ident
weakName = char '\''  >> name

variable :: Parser Expr
variable = fmap Var name

intLit :: Parser Int
intLit = fmap fromIntegral (try (Token.integer lexer))

natLit :: Parser Int
natLit = fmap fromIntegral (Token.natural lexer)

strLit :: Parser String
strLit = Token.stringLiteral lexer

whiteSpace :: Parser ()
whiteSpace = Token.whiteSpace lexer

symbol :: String -> Parser String
symbol = Token.symbol lexer

reservedOp :: String -> Parser ()
reservedOp = Token.reservedOp lexer

lambda :: Parser Expr
lambda = parens $ do
    reservedOp "\\"
    ns <- many1 name
    reservedOp "->"
    fmap (flip (foldr Abs) ns) expr

letpair :: Parser Expr
letpair = do
    reserved "let"
    ds <- many1 $ do
        reserved "val"
        i <- parens $ do
            x <- name
            y <- name
            pure (x,y)
        reservedOp "="
        fmap ((,) i) expr
    reserved "in"
    fmap (flip (foldr (uncurry Destruct)) ds) expr

pair :: Parser Expr
pair = parens $ do
    x <- expr
    reservedOp ","
    y <- expr
    pure (Pair x y)

annot :: Parser Expr
annot = parens $ do
    x <- expr
    reservedOp "::"
    y <- expr
    pure (Ann x y)

toMul :: Int -> Multiplicity
toMul x = case x of
    0 -> Zero
    _ -> Succ (toMul (x-1))

multiplicity :: Parser Multiplicity
multiplicity =
    fmap (const Omega) (reserved "w")
    <|> fmap toMul natLit

usage :: Parser Usage
usage = angles $ do
    m <- multiplicity
    reservedOp ","
    n <- multiplicity
    pure (Usage m n)

prodtype :: Parser Expr
prodtype = do
    (m,x,t) <- angles $ do
        m <- usage
        x <- name
        reservedOp "::"
        t <- expr
        pure (m,x,t)
    reservedOp "->"
    s <- expr
    pure (Prod (x,m) t s)

sumtype :: Parser Expr
sumtype = braces $ do
    m <- usage
    x <- name
    reservedOp "::"
    t <- expr
    reservedOp ","
    s <- expr
    pure (Sum (x,m) t s)

exprTerm :: Parser Expr
exprTerm =
    try lambda
    <|> try pair
    <|> try annot
    <|> try prodtype
    <|> sumtype
    <|> parens expr
    <|> variable
    <|> letpair
    <|> fmap (const Type) (reserved "Type")
    <|> fmap (const Unit) (reserved "Unit")
    <|> fmap (const Top) (reserved "Top")

appExpr :: Op Expr
appExpr = Infix space AssocLeft
    where
        space
            = whiteSpace
            >> notFollowedBy (choice (fmap reservedOp reservedOpNames))
            >> pure App

arrfun :: Expr -> Expr -> Expr
arrfun t s = Prod (Gen 0,Usage Omega Omega) t s

lolipop :: Expr -> Expr -> Expr
lolipop t s = Prod (Gen 0,Usage Omega rone) t s

binary :: String -> (a -> a -> a) -> Assoc -> Op a
binary o f a = flip Infix a $ do
    reservedOp o
    pure f

expr :: Parser Expr
expr = buildExpressionParser [[appExpr],[binary "->" arrfun AssocRight,binary "-o" lolipop AssocRight]] exprTerm

parseTL :: String -> String -> Either ParseError Expr
parseTL = parse expr