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
import Text.Parsec.Token ( TokenParser )
import qualified Text.Parsec.Token as Token

impLanguageDef :: Token.LanguageDef s
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

parseImp :: String -> Either ParseError ImpProgram
parseImp str = runParser impProgram () "" str

impProgram :: ImpParser s ImpProgram
impProgram = do
  let impLexer = Token.makeTokenParser $ impLanguageDef
  stmts <- many1 $ (Token.whiteSpace impLexer >> statement impLexer)
  return $ seqList stmts

statement :: TokenParser s -> ImpParser s ImpProgram
statement lexer = (Token.parens lexer $ statement lexer)
              <|> (progParser $ parseIf lexer)
              <|> (progParser $ parseWhile lexer)
              <|> (progParser $ parseSkip lexer)
              <|> (progParser $ parseAsgn lexer)

seqList :: [ImpProgram] -> ImpProgram
seqList stmts = case stmts of
  []   -> impSkip
  s:[] -> s
  ss   -> impSeq ss

parseSkip :: TokenParser s -> ImpParser s ImpSkip
parseSkip lexer = do
  Token.reserved lexer "skip"
  _ <- Token.semi lexer
  return ImpSkip

parseAsgn :: TokenParser s -> ImpParser s ImpAsgn
parseAsgn lexer = do
  var <- name lexer
  Token.reservedOp lexer ":="
  expr <- parseAExp
  _ <- Token.semi lexer
  return $ ImpAsgn var expr

parseIf :: TokenParser s -> ImpParser s (ImpIf ImpProgram)
parseIf lexer = do
  Token.reserved lexer "if"
  cond  <- parseBExp
  Token.reserved lexer "then"
  tbranch <- many1 $ statement lexer
  ebranch <- option [] $
    (Token.reserved lexer "else" >>= \_ -> many1 $ statement lexer)
  Token.reserved lexer "endif"
  return $ ImpIf cond (seqList tbranch) (seqList ebranch)

parseWhile :: TokenParser s -> ImpParser s (ImpWhile ImpProgram)
parseWhile lexer = do
  Token.reserved lexer "while"
  cond  <- parseBExp
  Token.whiteSpace lexer
  Token.reserved lexer "do"
  inv <- option Nothing $ do
    Token.reserved lexer "@inv"
    invStr <- Token.braces lexer $ many $ noneOf "{}"
    case parseAssertion invStr of
      Left err  -> fail (show err)
      Right inv -> return $ Just inv
  var <- option Nothing $ do
    Token.reserved lexer "@var"
    varStr <- Token.braces lexer $ many $ noneOf "{}"
    case parseArith varStr of
      Left err  -> fail (show err)
      Right var -> return $ Just var
  Token.whiteSpace lexer
  body  <- many1 $ try $ statement lexer
  Token.whiteSpace lexer
  Token.reserved lexer "end"
  return $ ImpWhile cond (seqList body) (inv, var)

name :: TokenParser s -> ImpParser s Name
name lexer = Token.identifier lexer >>= (return . Name.fromString)

progParser :: ImpProgram_ p =>
              ImpParser s p -> ImpParser s ImpProgram
progParser stmtParser = do
  result <- stmtParser
  return $ packImp result
