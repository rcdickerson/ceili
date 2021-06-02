{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Ceili.Language.FunImp
  ( AExp(..)
  , BExp(..)
  , FunImpl(..)
  , FunImpCall(..)
  , FunImplEnv
  , FunImpProgram
  , Name(..)
  , impCall
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.AExp
import Ceili.Language.BExp
import Ceili.Language.Compose
import qualified Ceili.Language.Imp as Imp
import Ceili.Name ( CollectableNames(..)
                  , Handle
                  , MappableNames(..) )
import Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Set as Set


------------------------------
-- Function Implementations --
------------------------------

data FunImpl = FunImpl { fimpl_params :: [Name]
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


--------------------
-- Function Calls --
--------------------

type CallId = String

data FunImpCall e = FunImpCall CallId [Imp.AExp] [Name]
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

type FunImpProgram = Imp.ImpExpr ( FunImpCall
                               :+: Imp.ImpSkip
                               :+: Imp.ImpAsgn
                               :+: Imp.ImpSeq
                               :+: Imp.ImpIf
                               :+: Imp.ImpWhile )

instance CollectableNames FunImpProgram where
  namesIn (Imp.In f) = namesIn f

instance MappableNames FunImpProgram where
  mapNames func (Imp.In f) = Imp.In $ mapNames func f

impCall :: (FunImpCall :<: f) => CallId -> [Imp.AExp] -> [Name] -> Imp.ImpExpr f
impCall cid args assignees = Imp.inject $ FunImpCall cid args assignees


-----------------
-- Interpreter --
-----------------

type FunImplEnv = Map Handle FunImpl

-- Interpreter is very similar to Imp's, but has to thread through a function
-- implementation context.
-- TODO: Might be worthwhile to abstract interpreters over some context object?

class EvalFunImp f where
  evalFunImp :: FunImplEnv -> State -> Imp.Fuel -> f -> Ceili (Maybe State)

instance EvalFunImp (Imp.ImpSkip e) where
  evalFunImp _ st fuel e = return $ Imp.evalImp st fuel e

instance EvalFunImp (Imp.ImpAsgn e) where
  evalFunImp _ st fuel e = return $ Imp.evalImp st fuel e

instance EvalFunImp e => EvalFunImp (Imp.ImpSeq e) where
  evalFunImp impls st fuel (Imp.ImpSeq stmts) =
    case stmts of
      [] -> return $ Just st
      (stmt:rest) -> do
        mSt' <- evalFunImp impls st fuel stmt
        case mSt' of
          Nothing -> return Nothing
          Just st' -> evalFunImp impls st' fuel (Imp.ImpSeq rest)

instance EvalFunImp e => EvalFunImp (Imp.ImpIf e) where
  evalFunImp impls st fuel (Imp.ImpIf c t f) =
    if (evalBExp st c)
    then (evalFunImp impls st fuel t)
    else (evalFunImp impls st fuel f)

instance EvalFunImp e => EvalFunImp (Imp.ImpWhile e) where
  evalFunImp impls st fuel (Imp.ImpWhile cond body meta) =
    case (evalBExp st cond) of
      False -> return $ Just st
      True  -> case fuel of
        Imp.InfiniteFuel   -> step Imp.InfiniteFuel
        Imp.Fuel n | n > 0 -> step $ Imp.Fuel (n - 1)
        _                  -> do log_e $ "Ran out of fuel"
                                 return Nothing
    where
      step fuel' = do
        mSt' <- evalFunImp impls st fuel' body
        case mSt' of
          Nothing  -> return Nothing
          Just st' -> evalFunImp impls st' fuel' (Imp.ImpWhile cond body meta)

instance EvalFunImp (FunImpCall e) where
  evalFunImp impls st fuel (FunImpCall cid args assignees) =
    case Map.lookup cid impls of
      Just (FunImpl params body returns) -> do
        let eargs = map (evalAExp st) args
        let inputSt = Map.fromList $ zip params eargs
        result <- evalFunImp impls inputSt fuel body
        return $ case result of
          Nothing -> Nothing
          Just outputSt -> let
            retVals = map (\r -> Map.findWithDefault 0 r outputSt) returns
            assignments = Map.fromList $ zip assignees retVals
            in Just $ Map.union assignments st
      Nothing -> do
        log_e $ "No implementation for " ++ cid
        return Nothing

instance (EvalFunImp (f e), EvalFunImp (g e)) => EvalFunImp ((f :+: g) e) where
  evalFunImp impls st fuel (Inl f) = evalFunImp impls st fuel f
  evalFunImp impls st fuel (Inr g) = evalFunImp impls st fuel g

instance EvalFunImp FunImpProgram where
  evalFunImp impls st fuel (Imp.In f) = evalFunImp impls st fuel f
