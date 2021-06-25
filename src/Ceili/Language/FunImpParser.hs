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
                       ++ ["fun", "return"]
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
        <|> ImpParser.parseIf lexer statement
        <|> ImpParser.parseWhile lexer statement
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
  retExprs  <- option [ALit 0] returnStatement
  let freshIds = Name.buildFreshIds $ namesIn (Imp.ImpSeq bodyStmts)
      retVal   = Name (cid ++ "!retVal") 0
      retNames = snd $ foldr (\_ (ids, names) ->
                                 let (ids', nextFresh) = Name.runFreshen ids retVal
                                 in  (ids', nextFresh:names))
                       (freshIds, [])
                       retExprs
      asgns    = map (uncurry Imp.impAsgn) $ zip retNames retExprs
      body     = bodyStmts ++ asgns
  return (Imp.impSeq body, retNames)

returnStatement :: FunImpParser [AExp]
returnStatement = do
  reserved "return"
  retExprs <- try varArrayOrAExp
          <|> aexpTuple
  _ <- semi
  return retExprs

funCall :: ProgramParser
funCall = do
  assignees <- (try nameTuple) <|> nameArrayOrName
  reservedOp ":="
  funName <- identifier
  args    <- aexpTuple
  _ <- semi
  return $ impCall funName args assignees

nameTuple :: FunImpParser [Name]
nameTuple = do
  names <- parens $ sepBy nameArrayOrName comma
  return $ concat names

nameArray :: FunImpParser [Name]
nameArray = do
  var <- name
  char '[' >> whiteSpace
  num <- integer
  char ']' >> whiteSpace
  return $ case num of
    0 -> [ var ]
    _ -> let (Name vname i) = var
         in map (\n -> Name (vname ++ "_" ++ (show n)) i) [0..(num-1)]

nameArrayOrName :: FunImpParser [Name]
nameArrayOrName = (try nameArray) <|> (do n <- name; return [n])

varArray :: FunImpParser [AExp]
varArray = do
  names <- nameArray
  return $ map AVar names

aexpTuple :: FunImpParser [AExp]
aexpTuple = do
  args <- parens $ sepBy varArrayOrAExp comma
  return $ concat args

varArrayOrAExp :: FunImpParser [AExp]
varArrayOrAExp = (try varArray) <|> (do aexp <- parseAExp; return [aexp])

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
