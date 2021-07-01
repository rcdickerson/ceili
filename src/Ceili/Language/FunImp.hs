{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Ceili.Language.FunImp
  ( AExp(..)
  , BExp(..)
  , CallId
  , Fuel(..)
  , FunEvalContext(..)
  , FunImpl(..)
  , FunImplEnv
  , FunImpProgram
  , ImpAsgn(..)
  , ImpCall(..)
  , ImpExpr(..)
  , ImpIf(..)
  , ImpSkip(..)
  , ImpSeq(..)
  , ImpWhile(..)
  , Name(..)
  , State
  , impBackwardPT
  , impAsgn
  , impCall
  , impIf
  , impSeq
  , impSkip
  , impWhile
  , impWhileWithMeta
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
import Control.Monad ( foldM )
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

data ImpCall e = ImpCall CallId [AExp] [Name]
                deriving (Eq, Ord, Show, Functor)

instance CollectableNames (ImpCall e) where
  namesIn (ImpCall _ args assignees) =
    Set.union (namesIn args) (namesIn assignees)

instance FreshableNames (ImpCall e) where
  freshen (ImpCall cid args assignees) = do
    args'      <- freshen args
    assignees' <- freshen assignees
    return $ ImpCall cid args' assignees'

instance MappableNames (ImpCall e) where
  mapNames f (ImpCall cid args assignees) =
    ImpCall cid (map (mapNames f) args) (map f assignees)


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

instance MappableNames FunImpProgram where
  mapNames func (In f) = In $ mapNames func f

instance FreshableNames FunImpProgram where
  freshen (In f) = return . In =<< freshen f

impCall :: (ImpCall :<: f) => CallId -> [AExp] -> [Name] -> ImpExpr f
impCall cid args assignees = inject $ ImpCall cid args assignees


-----------------
-- Interpreter --
-----------------

data FunEvalContext = FunEvalContext { fiec_fuel  :: Fuel
                                     , fiec_impls :: FunImplEnv
                                     }

instance FuelTank FunEvalContext where
  getFuel = fiec_fuel
  setFuel (FunEvalContext _ impls) fuel = FunEvalContext fuel impls

instance EvalImp FunEvalContext (ImpCall e) where
  evalImp ctx st (ImpCall cid args assignees) =
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

instance EvalImp FunEvalContext FunImpProgram where
  evalImp ctx st (In f) = evalImp ctx st f


-----------------
-- Test States --
-----------------

instance PopulateTestStates FunEvalContext (ImpCall e) where
  populateTestStates _ _ = return . id

instance PopulateTestStates FunEvalContext FunImpProgram where
  populateTestStates ctx sts (In f) = populateTestStates ctx sts f >>= return . In


-- TODO: PTSes don't handle recursion. Add detection to fail gracefully instead of
-- spinning forever.

----------------------------------
-- Backward Predicate Transform --
----------------------------------

instance ImpBackwardPT FunImplEnv (ImpCall e) where
  impBackwardPT impls (ImpCall cid args assignees) post =
    case Map.lookup cid impls of
      Nothing   -> throwError $ "No implementation for " ++ cid
      Just impl -> do
        FunImpl params body returns <- envFreshen impl
        post' <- assignBackward impls assignees (map AVar returns) post
        wp    <- impBackwardPT impls body post'
        wp'   <- assignBackward impls params args wp
        return wp'

instance ImpBackwardPT FunImplEnv FunImpProgram where
  impBackwardPT ctx (In f) post = impBackwardPT ctx f post

assignBackward :: FunImplEnv -> [Name] -> [AExp] -> Assertion -> Ceili Assertion
assignBackward impls params args post =
  if length params /= length args
    then throwError "Different number of params and args"
    else do
      let doAsgn post' (a1, a2) = impBackwardPT impls (ImpAsgn a1 a2) post'
      foldM doAsgn post $ zip params args


----------------------------------
-- Forward Predicate Transform --
----------------------------------

instance ImpForwardPT FunImplEnv (ImpCall e) where
  impForwardPT impls (ImpCall cid args assignees) pre =
    case Map.lookup cid impls of
      Nothing -> throwError $ "No implementation for " ++ cid
      Just impl -> do
        FunImpl params body returns <- envFreshen impl
        pre' <- assignForward impls params args pre
        sp   <- impForwardPT impls body pre'
        sp'  <- assignForward impls assignees (map AVar returns) sp
        return sp'

instance ImpForwardPT FunImplEnv FunImpProgram where
  impForwardPT ctx (In f) pre = impForwardPT ctx f pre

assignForward :: FunImplEnv -> [Name] -> [AExp] -> Assertion -> Ceili Assertion
assignForward impls params args pre =
  if length params /= length args
    then throwError "Different number of params and args"
    else do
      let doAsgn pre' (a1, a2) = impForwardPT impls (ImpAsgn a1 a2) pre'
      foldM doAsgn pre $ zip params args
