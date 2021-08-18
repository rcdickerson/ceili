{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.TestUtil
  ( assertEquivalent
  , assertHasSameItems
  , assertImplies
  , assertValid
  , envFunImp
  , envImp
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.FunImp
import Ceili.Language.Imp
import Ceili.Literal
import Ceili.Name
import qualified Ceili.SMT as SMT
import Ceili.SMTString ( showSMT )
import qualified Data.Map as Map
import Data.Vector ( Vector )
import qualified Data.Vector as Vector
import System.Log.FastLogger
import Test.Framework

envImp :: ImpProgram -> Env
envImp prog = defaultEnv (typedNamesIn prog) (litsIn prog)

envFunImp :: FunImpProgram -> Env
envFunImp prog = defaultEnv (typedNamesIn prog) (litsIn prog)

assertValid :: Assertion -> IO ()
assertValid assertion = do
  result <- withFastLogger LogNone $ \logger ->
            SMT.checkValidFL logger assertion
  case result of
    SMT.Valid        -> return () -- pass
    SMT.Invalid s    -> assertFailure $ "Invalid: " ++ s
    SMT.ValidUnknown -> assertFailure "Unable to validate, solver returned UNK."

assertImplies :: Assertion -> Assertion -> IO ()
assertImplies a1 a2 = do
  let imp = Imp a1 a2
  result <- withFastLogger LogNone $ \logger ->
            SMT.checkValidFL logger imp
  case result of
    SMT.Valid        -> return () -- pass
    SMT.Invalid s    -> assertFailure $ unlines ["Invalid implication: ", showSMT a1, "=>", showSMT a2, "model:", s]
    SMT.ValidUnknown -> assertFailure "Unable to establish implication, solver returned UNK."

assertEquivalent :: Assertion -> Assertion -> IO ()
assertEquivalent a1 a2 = do
  let iff = And [ Imp a1 a2, Imp a2 a1 ]
  result <- withFastLogger LogNone $ \logger ->
            SMT.checkValidFL logger iff
  case result of
    SMT.Valid        -> return () -- pass
    SMT.Invalid s    -> assertFailure $ unlines ["Not equivalent: ", showSMT a1, "and", showSMT a2, "model:", s]
    SMT.ValidUnknown -> assertFailure "Unable to establish equivalence, solver returned UNK."

assertHasSameItems :: (Ord a, Show a) => Vector a -> Vector a -> IO ()
assertHasSameItems expectedVec actualVec = let
  addToCount item counts = let current = Map.findWithDefault 0 item counts
                           in Map.insert item (current + 1) counts
  countItems = Vector.foldr addToCount Map.empty
  in assertEqual (countItems expectedVec) (countItems actualVec)
