{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.FeatureLearning.SeparatorTest(htf_thisModulesTests) where

import Ceili.TestUtil
import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.FeatureLearning.Separator
import Ceili.InvariantInference.LinearInequalities
import Ceili.Name
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Vector as Vector

runAndAssertEquivalent :: Assertion -> Ceili (Maybe Assertion) -> IO ()
runAndAssertEquivalent expected actual = do
  result <- runCeili emptyEnv actual
  case result of
    Left err         -> assertFailure err
    Right mAssertion ->
      case mAssertion of
        Nothing     -> assertFailure "Expected assertion, got Nothing."
        Just actual -> assertEquivalent expected actual


test_featureLearn = let
  x         = TypedName (Name "x" 0) Int
  names     = Set.singleton x
  lits      = Set.fromList [1, 5, -1, -5]
  goodTests = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                              , Map.fromList [(Name "x" 0, 5)] ]
  badTests  = Vector.fromList [ Map.fromList [(Name "x" 0, -1)]
                              , Map.fromList [(Name "x" 0, -5)] ]
  expected  = Lt (Num 0) (Var x)
  in runAndAssertEquivalent expected $ findSeparator 1 (linearInequalities names lits) goodTests badTests
