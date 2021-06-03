{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Ceili.Language.FunImp
  ( AExp(..)
  , BExp(..)
  , FunImpl(..)
  , FunImpCall(..)
  , FunImplEnv
  , FunImpProgram
  , FunSpec(..)
  , FunSpecEnv
  , Name(..)
  , impCall
  , instantiateSpec
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

type FunImplEnv = Map Handle FunImpl


-----------------------------
-- Function Specifications --
-----------------------------

data FunSpec = FunSpec { fspec_params  :: [Name]
                       , fspec_returns :: [Name]
                       , fspec_pre     :: Assertion
                       , fspec_post    :: Assertion
                       }

instantiateSpec :: FunSpec -> [Arith] -> [Name] -> (Assertion, Assertion)
instantiateSpec (FunSpec params returns pre post) args assignees =
  let
    toInts  = map (\n -> TypedName n Int)
    subParams  assertion = foldr (uncurry subArith) assertion $ zip (toInts params) args
    subReturns assertion = foldr (uncurry substitute) assertion $ zip returns assignees
    subAll = subReturns . subParams
  in (subAll pre, subAll post)

instance CollectableNames FunSpec where
  namesIn (FunSpec params returns pre post) =
    Set.unions [ Set.fromList params
               , Set.fromList returns
               , namesIn pre
               , namesIn post ]

instance MappableNames FunSpec where
  mapNames f (FunSpec params returns pre post) =
    FunSpec (map f params) (map f returns) (mapNames f pre) (mapNames f post)

type FunSpecEnv = Map Handle FunSpec


--------------------
-- Function Calls --
--------------------

type CallId = String

data FunImpCall e = FunImpCall CallId [AExp] [Name]
                deriving (Eq, Ord, Show, Functor)

instance CollectableNames (FunImpCall e) where
  namesIn (FunImpCall _ args assignees) =
    Set.union (namesIn args) (namesIn assignees)

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


----------------------------------
-- Backward Predicate Transform --
----------------------------------

instance ImpBackwardPT FunSpecEnv (FunImpCall e) where
  impBackwardPT specs (FunImpCall cid args assignees) post =
    case Map.lookup cid specs of
      Nothing -> throwError $ "No specification for " ++ cid
      Just (FunSpec params returns pre post) -> do
        error ""

instance ImpBackwardPT FunSpecEnv FunImpProgram where
  impBackwardPT specs (In f) post = impBackwardPT specs f post


----------------------------------
-- Forward Predicate Transform --
----------------------------------

instance ImpForwardPT FunSpecEnv (FunImpCall e) where
  impForwardPT specs (FunImpCall cid args assignees) pre =
    case Map.lookup cid specs of
      Nothing -> throwError $ "No specification for " ++ cid
      Just (FunSpec params returns pre post) -> do
        error ""

instance ImpForwardPT FunSpecEnv FunImpProgram where
  impForwardPT specs (In f) pre = impForwardPT specs f pre
