{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Ceili.Language.FunImp
  ( FunImplEnv
  , FunImpProgram
  , fimpAsgn
  , fimpCall
  , fimpIf
  , fimpSeq
  , fimpSkip
  , fimpWhile
  ) where

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

pack :: FunImpProgram_ p => p -> FunImpProgram
pack = FunImpProgram

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
instance FunImpProgram_ (Imp.ImpIf FunImpProgram)
instance FunImpProgram_ (Imp.ImpWhile FunImpProgram)

fimpSkip :: FunImpProgram
fimpSkip = pack Imp.ImpSkip

fimpAsgn :: Name -> Imp.AExp -> FunImpProgram
fimpAsgn name aexp = pack $ Imp.ImpAsgn name aexp

fimpSeq :: [FunImpProgram] -> FunImpProgram
fimpSeq = pack . Imp.ImpSeq

fimpIf :: Imp.BExp -> FunImpProgram -> FunImpProgram -> FunImpProgram
fimpIf bexp t e = pack $ Imp.ImpIf bexp t e

fimpWhile :: Imp.BExp
          -> FunImpProgram
          -> (Maybe Imp.Invariant, Maybe Imp.Measure)
          -> FunImpProgram
fimpWhile bexp body iv = pack $ Imp.ImpWhile bexp body iv


------------------------------
-- Function Implementations --
------------------------------

data FunImpl = FunImpl { fimple_params :: [Name]
                       , fimpl_body    :: Imp.ImpProgram
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

data SCall = SCall CallId [Imp.AExp] [Name]
             deriving (Eq, Show)

instance FunImpProgram_ SCall

fimpCall :: CallId -> [Imp.AExp] -> [Name] -> FunImpProgram
fimpCall cid args assignees = pack $ SCall cid args assignees

instance CollectableNames SCall where
  namesIn (SCall _ args assignees) =
    Set.union (namesIn args) (namesIn assignees)

instance MappableNames SCall where
  mapNames f (SCall cid args assignees) =
    SCall cid (map (mapNames f) args) (map f assignees)
