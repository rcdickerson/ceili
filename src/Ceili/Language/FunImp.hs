{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Ceili.Language.FunImp
  ( AExp(..)
  , BExp(..)
  , FunImpl(..)
  , FunImpCall(..)
  , FunImplEnv
  , FunImpProgram
  , FunImpProgram_
  , Name(..)
  , fimpAsgn
  , fimpCall
  , fimpIf
  , fimpSeq
  , fimpSkip
  , fimpWhile
  , packFunImp
  ) where

import Ceili.Language.AExp
import Ceili.Language.BExp
import qualified Ceili.Language.Imp as Imp
import Ceili.Name ( CollectableNames(..)
                  , Handle
                  , MappableNames(..)
                  , Name(..) )
import Data.Map ( Map )
import qualified Data.Set as Set
import Data.Typeable ( Typeable, cast )


class ( CollectableNames p
      , MappableNames p
      , Eq p, Show p
      , Typeable p
      ) => FunImpProgram_ p

data FunImpProgram = forall p. FunImpProgram_ p => FunImpProgram p

packFunImp :: FunImpProgram_ p => p -> FunImpProgram
packFunImp = FunImpProgram

instance Eq FunImpProgram where
  (FunImpProgram p1) == (FunImpProgram p2) = Just p1 == cast p2
instance Show FunImpProgram where
  show (FunImpProgram p) = show p
instance CollectableNames FunImpProgram where
  namesIn (FunImpProgram p) = namesIn p
instance MappableNames FunImpProgram where
  mapNames f (FunImpProgram p) = FunImpProgram $ mapNames f p

-- Include normal Imp statements.
instance FunImpProgram_ Imp.ImpSkip
instance FunImpProgram_ Imp.ImpAsgn
instance FunImpProgram_ (Imp.ImpSeq FunImpProgram)
instance FunImpProgram_ (Imp.ImpSeq Imp.ImpProgram)
instance FunImpProgram_ (Imp.ImpIf FunImpProgram)
instance FunImpProgram_ (Imp.ImpIf Imp.ImpProgram)
instance FunImpProgram_ (Imp.ImpWhile FunImpProgram)
instance FunImpProgram_ (Imp.ImpWhile Imp.ImpProgram)

fimpSkip :: FunImpProgram
fimpSkip = packFunImp Imp.ImpSkip

fimpAsgn :: Name -> Imp.AExp -> FunImpProgram
fimpAsgn name aexp = packFunImp $ Imp.ImpAsgn name aexp

fimpSeq :: [FunImpProgram] -> FunImpProgram
fimpSeq = packFunImp . Imp.ImpSeq

fimpIf :: Imp.BExp -> FunImpProgram -> FunImpProgram -> FunImpProgram
fimpIf bexp t e = packFunImp $ Imp.ImpIf bexp t e

fimpWhile :: Imp.BExp
          -> FunImpProgram
          -> (Maybe Imp.Invariant, Maybe Imp.Measure)
          -> FunImpProgram
fimpWhile bexp body iv = packFunImp $ Imp.ImpWhile bexp body iv


------------------------------
-- Function Implementations --
------------------------------

data FunImpl = FunImpl { fimple_params :: [Name]
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

data FunImpCall = FunImpCall CallId [Imp.AExp] [Name]
                deriving (Eq, Show)

instance FunImpProgram_ FunImpCall

fimpCall :: CallId -> [Imp.AExp] -> [Name] -> FunImpProgram
fimpCall cid args assignees = packFunImp $ FunImpCall cid args assignees

instance CollectableNames FunImpCall where
  namesIn (FunImpCall _ args assignees) =
    Set.union (namesIn args) (namesIn assignees)

instance MappableNames FunImpCall where
  mapNames f (FunImpCall cid args assignees) =
    FunImpCall cid (map (mapNames f) args) (map f assignees)
