{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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

import Ceili.Language.AExp
import Ceili.Language.BExp
import Ceili.Language.Compose
import qualified Ceili.Language.Imp as Imp
import Ceili.Name ( CollectableNames(..)
                  , Handle
                  , MappableNames(..)
                  , Name(..) )
import Ceili.PTS ( BackwardPT(..), ForwardPT(..) )
import Data.Map ( Map )
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

type FunImplEnv = Map Handle FunImpl


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
