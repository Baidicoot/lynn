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
        ++ [".",",","(->)","->","%","!","^"]
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
    fmap (flip (foldr (uncurry Unpair)) ds) expr

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

multiplicity :: Parser Affine
multiplicity =
    fmap (const Omega) (reservedOp "!")
    <|> fmap Affine (reservedOp "^" >> natLit)
    <|> fmap Linear natLit

usage :: Parser Usage
usage = angles $ do
    m <- multiplicity
    reservedOp ","
    n <- multiplicity
    pure (Usage m n)

prodtype :: Parser Expr
prodtype = do
    (x,t) <- angles $ do
        x <- name
        reservedOp "::"
        t <- expr
        pure (x,t)
    reservedOp "->"
    s <- expr
    pure (Prod x t s)

sumtype :: Parser Expr
sumtype = braces $ do
    x <- name
    reservedOp "::"
    t <- expr
    reservedOp ","
    s <- expr
    pure (Sum x t s)

attr :: Parser Expr
attr = do
    m <- usage
    reservedOp "%"
    b <- exprTerm
    pure (Attr b m)

exprTerm :: Parser Expr
exprTerm =
    try lambda
    <|> try pair
    <|> try annot
    <|> parens expr
    <|> try attr
    <|> try prodtype
    <|> sumtype
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
arrfun = Prod (Gen 0)

lolipop :: Expr -> Expr -> Expr
lolipop t = Prod (Gen 0) (Attr t (Usage Omega (Linear 1)))

starpop :: Expr -> Expr -> Expr
starpop t = Prod (Gen 0) (Attr t (Usage (Linear 1) rzero))

binary :: String -> (a -> a -> a) -> Assoc -> Op a
binary o f a = flip Infix a $ do
    reservedOp o
    pure f

expr :: Parser Expr
expr = buildExpressionParser [[appExpr],[binary "-*" starpop AssocRight,binary "->" arrfun AssocRight,binary "-o" lolipop AssocRight]] exprTerm

parseTL :: String -> String -> Either ParseError Expr
parseTL = parse expr