{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Ceili.Language.FunImp
  ( AExp(..)
  , BExp(..)
  , Fuel(..)
  , FunImpl(..)
  , FunImpCall(..)
  , FunImplEnv
  , FunImpProgram
  , Name(..)
  , impBackwardPT
  , impCall
  , impForwardPT
  , populateTestStates
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.AExp
import Ceili.Language.BExp
import Ceili.Language.Compose
import Ceili.Language.Imp
import Ceili.Name
import Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Set as Set


------------------------------
-- Function Implementations --
------------------------------

data FunImpl = FunImpl { fimpl_params  :: [Name]
                       , fimpl_body    :: FunImpProgram
                       , fimpl_returns :: [Name]
                       } deriving (Eq, Show)

instance CollectableNames FunImpl where
  namesIn (FunImpl params body returns) =
    Set.unions [ Set.fromList params
               , namesIn body
               , Set.fromList returns ]

instance MappableNames FunImpl where
  mapNames f (FunImpl params body returns) =
    FunImpl (map f params) (mapNames f body) (map f returns)

instance FreshableNames FunImpl where
  freshen (FunImpl params body returns) = do
    params'  <- freshen params
    body'    <- freshen body
    returns' <- freshen returns
    return $ FunImpl params' body' returns'

type FunImplEnv = Map Handle FunImpl


--------------------
-- Function Calls --
--------------------

type CallId = String

data FunImpCall e = FunImpCall CallId [AExp] [Name]
                deriving (Eq, Ord, Show, Functor)

instance CollectableNames (FunImpCall e) where
  namesIn (FunImpCall _ args assignees) =
    Set.union (namesIn args) (namesIn assignees)

instance FreshableNames (FunImpCall e) where
  freshen (FunImpCall cid args assignees) = do
    args'      <- freshen args
    assignees' <- freshen assignees
    return $ FunImpCall cid args' assignees'

instance MappableNames (FunImpCall e) where
  mapNames f (FunImpCall cid args assignees) =
    FunImpCall cid (map (mapNames f) args) (map f assignees)


---------------------
-- FunImp Language --
---------------------

type FunImpProgram = ImpExpr ( FunImpCall
                           :+: ImpSkip
                           :+: ImpAsgn
                           :+: ImpSeq
                           :+: ImpIf
                           :+: ImpWhile )

instance CollectableNames FunImpProgram where
  namesIn (In f) = namesIn f

instance MappableNames FunImpProgram where
  mapNames func (In f) = In $ mapNames func f

instance FreshableNames FunImpProgram where
  freshen (In f) = return . In =<< freshen f

impCall :: (FunImpCall :<: f) => CallId -> [AExp] -> [Name] -> ImpExpr f
impCall cid args assignees = inject $ FunImpCall cid args assignees


-----------------
-- Interpreter --
-----------------

data FunEvalCtx = FunEvalCtx { fiec_fuel  :: Fuel
                             , fiec_impls :: FunImplEnv
                             }

instance FuelTank FunEvalCtx where
  getFuel = fiec_fuel
  setFuel (FunEvalCtx _ impls) fuel = FunEvalCtx fuel impls

instance EvalImp FunEvalCtx (FunImpCall e) where
  evalImp ctx st (FunImpCall cid args assignees) =
    let impls = fiec_impls ctx
    in case Map.lookup cid impls of
      Nothing -> do
        log_e $ "No implementation for " ++ cid
        return Nothing
      Just (FunImpl params body returns) -> do
        let eargs = map (evalAExp st) args
        let inputSt = Map.fromList $ zip params eargs
        result <- evalImp ctx inputSt body
        return $ case result of
          Nothing -> Nothing
          Just outputSt -> let
            retVals = map (\r -> Map.findWithDefault 0 r outputSt) returns
            assignments = Map.fromList $ zip assignees retVals
            in Just $ Map.union assignments st

instance EvalImp FunEvalCtx FunImpProgram where
  evalImp ctx st (In f) = evalImp ctx st f


-----------------
-- Test States --
-----------------

instance PopulateTestStates FunEvalCtx (FunImpCall e) where
  populateTestStates _ _ = return . id

instance PopulateTestStates FunEvalCtx FunImpProgram where
  populateTestStates ctx sts (In f) = populateTestStates ctx sts f >>= return . In


-----------------
-- PTS Context --
-----------------

data PTSContext = PTSContext
  { ptsc_funImpls :: FunImplEnv
  , ptsc_freshIds :: NextFreshIds
  }


----------------------------------
-- Backward Predicate Transform --
----------------------------------

instance ImpBackwardPT PTSContext (FunImpCall e) where
  impBackwardPT (PTSContext impls freshIds)
                (FunImpCall cid args assignees)
                post =
    case Map.lookup cid impls of
      Nothing   -> throwError $ "No implementation for " ++ cid
      Just impl -> do
        let (nextIds', FunImpl params body returns) = runFreshen freshIds impl
        -- Create predicate equating returns and assignees
        -- wp <- impBackwardPT impls body -- pred /\ post
        -- Create predicate equating args and params
        -- return pred /\ wp
        error "Unimplemeted"

instance ImpBackwardPT PTSContext FunImpProgram where
  impBackwardPT ctx (In f) post = impBackwardPT ctx f post


----------------------------------
-- Forward Predicate Transform --
----------------------------------

instance ImpForwardPT PTSContext (FunImpCall e) where
  impForwardPT (PTSContext impls freshIds) (FunImpCall cid args assignees) pre =
    case Map.lookup cid impls of
      Nothing -> throwError $ "No specification for " ++ cid
      Just spec -> do
        error "unimplemented"

instance ImpForwardPT PTSContext FunImpProgram where
  impForwardPT ctx (In f) pre = impForwardPT ctx f pre
