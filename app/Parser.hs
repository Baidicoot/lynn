module Parser (parseTL,TL(..)) where

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

comma :: Parser String
comma = Token.comma lexer

colon :: Parser String
colon = Token.colon lexer

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
            comma
            y <- name
            pure (x,y)
        reservedOp "="
        fmap ((,) i) expr
    reserved "in"
    fmap (flip (foldr (uncurry Unpair)) ds) expr

pair :: Parser Expr
pair = parens $ do
    x <- expr
    comma
    y <- expr
    pure (Pair x y)

annot :: Parser Expr
annot = parens $ do
    x <- expr
    colon
    y <- expr
    pure (Ann x y)

multiplicity :: Parser Affine
multiplicity =
    fmap (const Omega) (reservedOp "!")
    <|> fmap (const Affine) (reservedOp "?")
    <|> fmap (const Linear) (reserved "1")
    <|> fmap (const Zero) (reserved "0")

explUsage :: Parser Usage
explUsage = angles $ do
    m <- multiplicity
    comma
    n <- multiplicity
    pure (Usage m n)

usage :: Parser Usage
usage =
    fmap (const (Usage Omega Linear)) (reservedOp "*")
    <|> fmap (const (Usage Linear Zero)) (reservedOp "~")
    <|> fmap (const (Usage Omega Affine)) (reservedOp "?")
    <|> fmap (const (Usage Omega Omega)) (reservedOp "!")
    <|> fmap (const (Usage Omega Zero)) (reservedOp "@")
    <|> explUsage

usageExpr :: Parser Expr
usageExpr = liftM2 (flip Attr) usage exprTerm

prodtype :: Parser Expr
prodtype = do
    (x,t) <- parens $ do
        x <- name
        colon
        t <- expr
        pure (x,t)
    reservedOp "->"
    s <- expr
    pure (Prod x t s)

sumtype :: Parser Expr
sumtype = braces $ do
    x <- name
    colon
    t <- expr
    comma
    s <- expr
    pure (Sum x t s)

exprTerm :: Parser Expr
exprTerm =
    try lambda
    <|> try pair
    <|> try prodtype
    <|> try annot
    <|> parens expr
    <|> try usageExpr
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
arrfun = Prod Hole

lolipop :: Expr -> Expr -> Expr
lolipop t = Prod Hole (Attr t (Usage Omega Linear))

starpop :: Expr -> Expr -> Expr
starpop t = Prod Hole (Attr t (Usage Linear rzero))

binary :: String -> (a -> a -> a) -> Assoc -> Op a
binary o f a = flip Infix a $ do
    reservedOp o
    pure f

expr :: Parser Expr
expr = buildExpressionParser [[appExpr],[binary "-*" starpop AssocRight,binary "->" arrfun AssocRight,binary "-o" lolipop AssocRight]] exprTerm

data TL
    = Assert Usage Ident Expr
    | Define Usage Ident Expr
    | Eval Usage Expr

tlExpr :: Parser TL
tlExpr =
    liftM3 Assert (reserved "assert" >> usage) name (colon >> expr)
    <|> liftM3 Define (reserved "define" >> usage) name (reservedOp "=" >> expr)
    <|> liftM2 Eval usage expr

parseTL :: String -> String -> Either ParseError TL
parseTL = parse tlExpr