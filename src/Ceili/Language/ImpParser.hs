{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module Ceili.Language.ImpParser
  ( ParseError
  , ProgramParser
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
import Ceili.Language.Compose
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

type ImpParser s a   = Parsec String s a
type ProgramParser s = ImpParser s ImpProgram

parseImp :: String -> Either ParseError ImpProgram
parseImp str = runParser impProgram () "" str

impProgram :: ProgramParser s
impProgram = do
  let impLexer = Token.makeTokenParser $ impLanguageDef
  stmts <- many1 $ (Token.whiteSpace impLexer >> statement impLexer)
  return $ impSeqIfNeeded stmts

type BasicImpProg f = ( ImpAsgn  :<: f
                      , ImpIf    :<: f
                      , ImpSeq   :<: f
                      , ImpSkip  :<: f
                      , ImpWhile :<: f)

statement :: BasicImpProg f => TokenParser s -> ImpParser s (ImpExpr f)
statement lexer = (Token.parens lexer $ statement lexer)
              <|> parseIf lexer
              <|> parseWhile lexer
              <|> parseSkip lexer
              <|> parseAsgn lexer

parseSkip :: ImpSkip :<: f => TokenParser s -> ImpParser s (ImpExpr f)
parseSkip lexer = do
  Token.reserved lexer "skip"
  _ <- Token.semi lexer
  return $ impSkip

parseAsgn :: ImpAsgn :<: f => TokenParser s -> ImpParser s (ImpExpr f)
parseAsgn lexer = do
  var <- name lexer
  Token.reservedOp lexer ":="
  expr <- parseAExp
  _ <- Token.semi lexer
  return $ impAsgn var expr

parseIf :: BasicImpProg f => TokenParser s -> ImpParser s (ImpExpr f)
parseIf lexer = do
  Token.reserved lexer "if"
  cond  <- parseBExp
  Token.reserved lexer "then"
  tbranch <- many1 $ statement lexer
  ebranch <- option [] $
    (Token.reserved lexer "else" >>= \_ -> many1 $ statement lexer)
  Token.reserved lexer "endif"
  return $ impIf cond (impSeqIfNeeded tbranch) (impSeqIfNeeded ebranch)

parseWhile :: BasicImpProg f => TokenParser s -> ImpParser s (ImpExpr f)
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
  return $ impWhile cond (impSeqIfNeeded body) (inv, var)

name :: TokenParser s -> ImpParser s Name
name lexer = Token.identifier lexer >>= (return . Name.fromString)
