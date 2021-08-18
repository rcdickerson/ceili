{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Ceili.Language.FunImp
  ( AExp(..)
  , BExp(..)
  , CallId
  , EvalImp(..)
  , Fuel(..)
  , FuelTank(..)
  , FunEvalContext(..)
  , FunImpl(..)
  , FunImplEnv
  , FunImplLookup(..)
  , FunImpProgram
  , ImpAsgn(..)
  , ImpBackwardPT(..)
  , ImpCall(..)
  , ImpExpr(..)
  , ImpForwardPT(..)
  , ImpIf(..)
  , ImpSkip(..)
  , ImpSeq(..)
  , ImpWhile(..)
  , ImpWhileMetadata(..)
  , PopulateTestStates(..)
  , Name(..)
  , State
  , impAsgn
  , impCall
  , impIf
  , impSeq
  , impSkip
  , impWhile
  , impWhileWithMeta
  , inject
  , prettyArgs
  , prettyAssignees
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.AExp
import Ceili.Language.BExp
import Ceili.Language.Compose
import Ceili.Language.Imp
import Ceili.Name
import Ceili.Literal
import Control.Monad ( foldM )
import Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prettyprinter


------------------------------
-- Function Implementations --
------------------------------

data FunImpl e = FunImpl { fimpl_params  :: [Name]
                         , fimpl_body    :: e
                         , fimpl_returns :: [Name]
                         } deriving (Eq, Show)

instance CollectableNames e => CollectableNames (FunImpl e) where
  namesIn (FunImpl params body returns) =
    Set.unions [ Set.fromList params
               , namesIn body
               , Set.fromList returns ]

instance CollectableTypedNames e => CollectableTypedNames (FunImpl e) where
  typedNamesIn (FunImpl params body returns) =
    Set.unions [ Set.fromList $ map (\n -> TypedName n Int) params
               , typedNamesIn body
               , Set.fromList $ map (\n -> TypedName n Int) returns ]

instance MappableNames e => MappableNames (FunImpl e) where
  mapNames f (FunImpl params body returns) =
    FunImpl (map f params) (mapNames f body) (map f returns)

instance FreshableNames e => FreshableNames (FunImpl e) where
  freshen (FunImpl params body returns) = do
    params'  <- freshen params
    body'    <- freshen body
    returns' <- freshen returns
    return $ FunImpl params' body' returns'

instance CollectableLiterals e => CollectableLiterals (FunImpl e) where
  litsIn (FunImpl _ body _) = litsIn body


------------------------------------------
-- Function Implementation Environments --
------------------------------------------

type FunImplEnv e = Map Handle (FunImpl e)

class FunImplLookup a e where
  lookupFunImpl :: a -> Handle -> Ceili (FunImpl e)

instance FunImplLookup (FunImplEnv e) e where
  lookupFunImpl env name = case Map.lookup name env of
      Nothing   -> throwError $ "No implementation for " ++ name
      Just impl -> return impl

instance CollectableNames e => CollectableNames (FunImplEnv e) where
  namesIn = namesIn . Map.elems


--------------------
-- Function Calls --
--------------------

type CallId = String

data ImpCall e = ImpCall CallId [AExp] [Name]
                deriving (Eq, Ord, Show, Functor)

instance CollectableNames (ImpCall e) where
  namesIn (ImpCall _ args assignees) =
    Set.union (namesIn args) (namesIn assignees)

instance CollectableTypedNames (ImpCall e) where
  typedNamesIn (ImpCall _ args assignees) =
    Set.union (typedNamesIn args) (Set.map (\n -> TypedName n Int) $ namesIn assignees)

instance FreshableNames (ImpCall e) where
  freshen (ImpCall cid args assignees) = do
    args'      <- freshen args
    assignees' <- freshen assignees
    return $ ImpCall cid args' assignees'

instance MappableNames (ImpCall e) where
  mapNames f (ImpCall cid args assignees) =
    ImpCall cid (map (mapNames f) args) (map f assignees)

instance CollectableLiterals (ImpCall e) where
  litsIn (ImpCall _ args _) = litsIn args


---------------------
-- FunImp Language --
---------------------

type FunImpProgram = ImpExpr ( ImpCall
                           :+: ImpSkip
                           :+: ImpAsgn
                           :+: ImpSeq
                           :+: ImpIf
                           :+: ImpWhile )

instance CollectableNames FunImpProgram where
  namesIn (In f) = namesIn f

instance CollectableTypedNames FunImpProgram where
  typedNamesIn (In f) = typedNamesIn f

instance MappableNames FunImpProgram where
  mapNames func (In f) = In $ mapNames func f

instance FreshableNames FunImpProgram where
  freshen (In f) = return . In =<< freshen f

instance CollectableLiterals FunImpProgram where
  litsIn (In f) = litsIn f

impCall :: (ImpCall :<: f) => CallId -> [AExp] -> [Name] -> ImpExpr f
impCall cid args assignees = inject $ ImpCall cid args assignees


-----------------
-- Interpreter --
-----------------

data FunEvalContext e = FunEvalContext { fiec_fuel  :: Fuel
                                       , fiec_impls :: FunImplEnv e
                                       }

instance FuelTank (FunEvalContext e) where
  getFuel = fiec_fuel
  setFuel (FunEvalContext _ impls) fuel = FunEvalContext fuel impls

instance FunImplLookup (FunEvalContext e) e where
  lookupFunImpl (FunEvalContext _ impls) name = case Map.lookup name impls of
    Nothing   -> throwError $ "No implementation for " ++ name
    Just impl -> return impl

instance (FunImplLookup c e, EvalImp c e) => EvalImp c (ImpCall e) where
  evalImp ctx st (ImpCall cid args assignees) = do
    (FunImpl params body returns) <- (lookupFunImpl ctx cid :: Ceili (FunImpl e))
    let eargs = map (evalAExp st) args
    let inputSt = Map.fromList $ zip params eargs
    result <- evalImp ctx inputSt body
    return $ case result of
      Nothing -> Nothing
      Just outputSt ->
        let
          retVals = map (\r -> Map.findWithDefault 0 r outputSt) returns
          assignments = Map.fromList $ zip assignees retVals
        in Just $ Map.union assignments st

-- TODO: Evaluating a function call should cost fuel to prevent infinite recursion.

instance EvalImp (FunEvalContext FunImpProgram) FunImpProgram where
  evalImp ctx st (In f) = evalImp ctx st f


-----------------
-- Test States --
-----------------

instance EvalImp (FunEvalContext e) e => PopulateTestStates (FunEvalContext e) (ImpCall e) where
  populateTestStates _ _ = return . id

instance PopulateTestStates (FunEvalContext FunImpProgram) FunImpProgram where
  populateTestStates ctx sts (In f) = populateTestStates ctx sts f >>= return . In


-- TODO: PTSes don't handle recursion. Add detection to fail gracefully instead of
-- spinning forever.


--------------------
-- Pretty Printer --
--------------------

instance Pretty (ImpCall e) where
  pretty (ImpCall callId args assignees) =
    prettyAssignees assignees <+> pretty ":=" <+> pretty callId <> prettyArgs args

prettyAssignees :: Pretty a => [a] -> Doc ann
prettyAssignees assignees =
  case assignees of
    []     -> pretty "??"
    (x:[]) -> pretty x
    _      -> encloseSep lparen rparen comma (map pretty assignees)

prettyArgs :: Pretty a => [a] -> Doc ann
prettyArgs args =
  case args of
    []     -> pretty "()"
    (x:[]) -> parens $ pretty x
    _      -> encloseSep lparen rparen comma (map pretty args)


instance Pretty FunImpProgram where
  pretty (In p) = pretty p


----------------------------------
-- Backward Predicate Transform --
----------------------------------

instance ImpBackwardPT (FunImplEnv FunImpProgram) FunImpProgram where
  impBackwardPT ctx (In f) post = impBackwardPT ctx f post

instance (FunImplLookup c e, ImpBackwardPT c e, FreshableNames e) => ImpBackwardPT c (ImpCall e) where
  impBackwardPT ctx (ImpCall cid args assignees) post = do
    (impl :: FunImpl e) <- lookupFunImpl ctx cid
    FunImpl params body returns <- envFreshen impl
    post' <- assignBackward ctx assignees (map AVar returns) post
    wp    <- impBackwardPT ctx body post'
    assignBackward ctx params args wp

assignBackward :: c -> [Name] -> [AExp] -> Assertion -> Ceili Assertion
assignBackward ctx params args post =
  if length params /= length args
    then throwError "Different number of params and args"
    else do
      let doAsgn post' (a1, a2) = impBackwardPT ctx (ImpAsgn a1 a2) post'
      foldM doAsgn post $ zip params args


----------------------------------
-- Forward Predicate Transform --
----------------------------------

instance ImpForwardPT (FunImplEnv FunImpProgram) FunImpProgram where
  impForwardPT ctx (In f) pre = impForwardPT ctx f pre

instance (FunImplLookup c e, ImpForwardPT c e, FreshableNames e) => ImpForwardPT c (ImpCall e) where
  impForwardPT ctx (ImpCall cid args assignees) pre = do
    (impl :: FunImpl e) <- lookupFunImpl ctx cid
    FunImpl params body returns <- envFreshen impl
    pre' <- assignForward ctx params args pre
    sp   <- impForwardPT ctx body pre'
    assignForward ctx assignees (map AVar returns) sp

assignForward :: c -> [Name] -> [AExp] -> Assertion -> Ceili Assertion
assignForward impls params args pre =
  if length params /= length args
    then throwError "Different number of params and args"
    else do
      let doAsgn pre' (a1, a2) = impForwardPT impls (ImpAsgn a1 a2) pre'
      foldM doAsgn pre $ zip params args
