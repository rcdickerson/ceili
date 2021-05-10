module Ceili.Language.FunImpParser
  ( ParseError
  , parseFunImp
  ) where

import Ceili.Language.AExp
import Ceili.Language.AExpParser ( parseAExp )
import Ceili.Language.FunImp
import qualified Ceili.Language.Imp as Imp
import qualified Ceili.Language.ImpParser as ImpParser
import Ceili.Name ( namesIn )
import qualified Ceili.Name as Name
import qualified Data.Map as Map
import Text.Parsec
import qualified Text.Parsec.Token as Token

type FunImpParser a = Parsec String FunImplEnv a
type ProgramParser = FunImpParser FunImpProgram

funImpLanguageDef :: Token.LanguageDef a
funImpLanguageDef = ImpParser.impLanguageDef {
    Token.reservedNames = Token.reservedNames ImpParser.impLanguageDef
                       ++ ["fun", "return", "call"]
  }

lexer      = Token.makeTokenParser funImpLanguageDef
braces     = Token.braces     lexer
comma      = Token.comma      lexer
identifier = Token.identifier lexer
integer    = Token.integer    lexer
parens     = Token.parens     lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
semi       = Token.semi       lexer
whiteSpace = Token.whiteSpace lexer

parseFunImp :: String -> Either ParseError FunImplEnv
parseFunImp str = runParser program Map.empty "" str

program :: FunImpParser FunImplEnv
program = do
  _ <- many1 $ whiteSpace >> funDef
  getState

statement :: ProgramParser
statement = parens statement
        <|> try funCall
        <|> ImpParser.parseIf lexer
        <|> ImpParser.parseWhile lexer
        <|> ImpParser.parseSkip lexer
        <|> ImpParser.parseAsgn lexer

funDef :: FunImpParser ()
funDef = do
  reserved "fun"
  handle <- identifier
  params <- nameTuple
  (body, rets) <- braces (funBody handle)
  recordFunDef handle params body rets

funBody :: Name.Handle -> FunImpParser (FunImpProgram, [Name])
funBody cid = do
  bodyStmts <- many statement
  reserved "return"
  retExprs <- (try varArray)
          <|> (try $ parseAExp >>= return . return)
          <|> aexpTuple
  _ <- semi
  let freshIds = Name.buildNextFreshIds $ namesIn (Imp.ImpSeq bodyStmts)
      retVal   = Name (cid ++ "!retVal") 0
      retNames = fst $ foldr (\_ (names, ids) ->
                                 let (nextFresh, ids') = Name.nextFreshName retVal ids
                                 in  (nextFresh:names, ids'))
                       ([], freshIds)
                       retExprs
      asgns    = map (uncurry Imp.impAsgn) $ zip retNames retExprs
      body     = bodyStmts ++ asgns
  return (Imp.impSeq body, retNames)

funCall :: ProgramParser
funCall = do
  assignees <- (try nameTuple) <|> nameArray
  reservedOp ":="
  reserved "call"
  funName <- identifier
  args    <- aexpTuple
  _ <- semi
  return $ impCall funName args assignees

nameTuple :: FunImpParser [Name]
nameTuple = do
  names <- parens $ sepBy nameArray comma
  return $ concat names

nameArray :: FunImpParser [Name]
nameArray = do
  (Name vname i, num) <- try (do
                         var <- name
                         char '[' >> whiteSpace
                         num <- integer
                         char ']' >> whiteSpace
                         return (var, num))
                     <|> (do var <- name; return (var, 0))
  return $ case num of
    0 -> [Name vname i]
    _ -> map (\n -> Name (vname ++ "_" ++ (show n)) i) [0..(num-1)]

varArray :: FunImpParser [AExp]
varArray = do
  names <- nameArray
  return $ map AVar names

aexpTuple :: FunImpParser [AExp]
aexpTuple = do
  args <- parens $ sepBy argument comma
  return $ concat args

argument :: FunImpParser [AExp]
argument = varArray <|> (parseAExp >>= return . return)

name :: FunImpParser Name
name = identifier >>= (return . Name.fromString)

recordFunDef :: Name.Handle
             -> [Name]
             -> FunImpProgram
             -> [Name]
             -> FunImpParser ()
recordFunDef handle params body rets = do
  funs <- getState
  putState $ Map.insert handle (FunImpl params body rets) funs
  return ()