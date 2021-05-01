module Ceili.Language.ImpParser
  ( ParseError
  , impLanguageDef
  , parseAsgn
  , parseIf
  , parseImp
  , parseSkip
  , parseWhile
  ) where

import Ceili.Assertion
import Ceili.Language.AExpParser ( parseAExp )
import Ceili.Language.BExpParser ( parseBExp )
import Ceili.Language.Imp
import qualified Ceili.Name as Name
import Text.Parsec
import qualified Text.Parsec.Token as Token

impLanguageDef :: Token.LanguageDef a
impLanguageDef = Token.LanguageDef
  { Token.caseSensitive   = True
  , Token.commentStart    = "/*"
  , Token.commentEnd      = "*/"
  , Token.commentLine     = "//"
  , Token.identStart      = letter <|> char '@'
  , Token.identLetter     = alphaNum <|> char '_'
  , Token.nestedComments  = True
  , Token.opStart         = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Token.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Token.reservedNames   = [ "if", "then", "else", "endif"
                            , "while", "do", "end"
                            , "@inv", "@var"
                            , "skip"
                            , "true", "false"
                            ]
  , Token.reservedOpNames = [":="]
  }

type ImpParser s a = Parsec String s a

lexer      = Token.makeTokenParser $ impLanguageDef
braces     = Token.braces     lexer
identifier = Token.identifier lexer
integer    = Token.integer    lexer
parens     = Token.parens     lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
semi       = Token.semi       lexer
whiteSpace = Token.whiteSpace lexer

parseImp :: String -> Either ParseError ImpProgram
parseImp str = runParser impProgram () "" str

impProgram :: ImpParser s ImpProgram
impProgram = do
  stmts <- many1 $ (whiteSpace >> statement)
  return $ seqList stmts

statement :: ImpParser s ImpProgram
statement = parens statement
        <|> progParser parseIf
        <|> progParser parseWhile
        <|> progParser parseSkip
        <|> progParser parseAsgn

seqList :: [ImpProgram] -> ImpProgram
seqList stmts = case stmts of
  []   -> impSkip
  s:[] -> s
  ss   -> impSeq ss

parseSkip :: ImpParser s ImpSkip
parseSkip = reserved "skip" >>
            semi >>
            return ImpSkip

parseAsgn :: ImpParser s ImpAsgn
parseAsgn = do
  var <- name
  reservedOp ":="
  expr <- parseAExp
  _ <- semi
  return $ ImpAsgn var expr

parseIf :: ImpParser s (ImpIf ImpProgram)
parseIf = do
  reserved "if"
  cond  <- parseBExp
  reserved "then"
  tbranch <- many1 statement
  ebranch <- option [] $ (reserved "else" >>= \_ -> many1 statement)
  reserved "endif"
  return $ ImpIf cond (seqList tbranch) (seqList ebranch)

parseWhile :: ImpParser s (ImpWhile ImpProgram)
parseWhile = do
  reserved "while"
  cond  <- parseBExp
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
  return $ ImpWhile cond (seqList body) (inv, var)

name :: ImpParser s Name
name = identifier >>= (return . Name.fromString)

progParser :: ImpProgram_ p =>
              ImpParser s p -> ImpParser s ImpProgram
progParser stmtParser = do
  result <- stmtParser
  return $ packImp result
