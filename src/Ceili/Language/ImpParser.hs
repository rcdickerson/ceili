-- A simple Imp parser.
-- Based on https://wiki.haskell.org/Parsing_a_simple_imperative_language

{-# LANGUAGE GADTs #-}

module Ceili.Language.ImpParser
  ( ParseError
  , parseImp
  ) where

import Ceili.Assertion
import Ceili.Language.Imp
import qualified Ceili.Name as Name
import Control.Monad
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token

languageDef :: LanguageDef ()
languageDef = Token.LanguageDef
  { Token.caseSensitive   = True
  , Token.commentStart    = "/*"
  , Token.commentEnd      = "*/"
  , Token.commentLine     = "//"
  , Token.identStart      = letter <|> char '@'
  , Token.identLetter     = alphaNum <|> char '_'
  , Token.nestedComments  = True
  , Token.opStart         = Token.opLetter languageDef
  , Token.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Token.reservedNames   = [ "if", "then", "else", "endif"
                            , "while", "do", "end"
                            , "@inv", "@var"
                            , "fun", "return", "call"
                            , "skip"
                            , "true", "false"
                            ]
  , Token.reservedOpNames = [ "+", "-", "*", "/", "%", "^"
                            , "==", "!=", "<=", ">=", "<", ">"
                            , "&&", "||", "!"
                            , ":="
                            ]
  }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens     lexer
braces     = Token.braces     lexer
integer    = Token.integer    lexer
comma      = Token.comma      lexer
semi       = Token.semi       lexer
whiteSpace = Token.whiteSpace lexer

type ImpParser a = Parsec String () a
type ProgramParser = ImpParser ImpProgram

parseImp :: String -> Either ParseError ImpProgram
parseImp str = runParser program () "" str

seqList :: [ImpProgram] -> ImpProgram
seqList stmts = case stmts of
  []   -> impSkip
  s:[] -> s
  ss   -> impSeq ss

program :: ProgramParser
program = do
  stmts <- many1 $ whiteSpace >> statement
  return $ seqList stmts

statement :: ProgramParser
statement =   parens statement
          <|> parseIf
          <|> parseWhile
          <|> parseSkip
          <|> parseAsgn

name :: ImpParser Name
name = identifier >>= (return . Name.fromString)

parseSkip :: ProgramParser
parseSkip = reserved "skip" >> semi >> return impSkip

parseAsgn :: ProgramParser
parseAsgn = do
  var <- name
  reservedOp ":="
  expr <- aExpression
  _ <- semi
  return $ impAsgn var expr

parseIf :: ProgramParser
parseIf = do
  reserved "if"
  cond  <- bExpression
  reserved "then"
  tbranch <- many1 statement
  ebranch <- option [] $ (reserved "else" >>= \_ -> many1 statement)
  reserved "endif"
  return $ impIf cond (seqList tbranch) (seqList ebranch)

parseWhile :: ProgramParser
parseWhile = do
  reserved "while"
  cond  <- bExpression
  whiteSpace
  reserved "do"
  inv <- option Nothing $ do
    reserved "@inv"
    invStr <- braces $ many $ noneOf "{}"
    case parseAssertion invStr of
      Left err  -> fail (show err)
      Right inv -> return $ Just inv
  var <- option Nothing $ do
    reserved "@var"
    varStr <- braces $ many $ noneOf "{}"
    case parseArith varStr of
      Left err  -> fail (show err)
      Right var -> return $ Just var
  whiteSpace
  body  <- many1 $ try statement
  whiteSpace
  reserved "end"
  return $ impWhile cond (seqList body) (inv, var)

aExpression :: ImpParser AExp
aExpression = buildExpressionParser aOperators aTerm

bExpression :: ImpParser BExp
bExpression = buildExpressionParser bOperators bTerm

aOperators = [ [Infix  (reservedOp "^" >> return APow) AssocLeft]
             , [Infix  (reservedOp "*" >> return AMul) AssocLeft,
                Infix  (reservedOp "/" >> return ADiv) AssocLeft,
                Infix  (reservedOp "%" >> return AMod) AssocLeft]
             , [Infix  (reservedOp "+" >> return AAdd) AssocLeft,
                Infix  (reservedOp "-" >> return ASub) AssocLeft]
              ]

bOperators = [ [Prefix (reservedOp "!" >> return BNot)]
             , [Infix  (reservedOp "&&" >> return BAnd) AssocLeft,
                Infix  (reservedOp "||"  >> return BOr)  AssocLeft]
             ]

aTerm =  parens aExpression
     <|> (name >>= return . AVar)
     <|> liftM ALit integer

bTerm =  parens bExpression
     <|> (reserved "true"  >> return (BTrue ))
     <|> (reserved "false" >> return (BFalse))
     <|> (try $ bBinop "==" BEq)
     <|> (try $ bBinop "!=" BNe)
     <|> (try $ bBinop "<=" BLe)
     <|> (try $ bBinop ">=" BGe)
     <|> (try $ bBinop "<"  BLt)
     <|> (try $ bBinop ">"  BGt)

bBinop :: String -> (AExp -> AExp -> BExp) -> ImpParser BExp
bBinop opStr opFun = do
  lhs <- aExpression
  reservedOp opStr
  rhs <- aExpression
  return $ opFun lhs rhs
