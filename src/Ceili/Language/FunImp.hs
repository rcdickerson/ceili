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
  , Name(..)
  , impCall
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.AExp
import Ceili.Language.BExp
import Ceili.Language.Compose
import Ceili.Language.Imp
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

type FunImplEnv = Map Handle FunImpl

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
      Nothing -> do
        log_e $ "No implementation for " ++ cid
        return Nothing

instance EvalImp FunEvalCtx FunImpProgram where
  evalImp ctx st (In f) = evalImp ctx st f
