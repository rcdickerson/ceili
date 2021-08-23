{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.InvariantInference.PieTest(htf_thisModulesTests) where

import Ceili.TestUtil
import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.InvariantInference.Pie
import Ceili.Name
import Control.Monad.Trans.State ( evalStateT )
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
        Nothing        -> assertFailure "Expected assertion, got Nothing."
        Just assertion -> assertEquivalent expected assertion


test_pie = let
  x         = TypedName (Name "x" 0) Int
  names     = Set.singleton x
  lits      = Set.empty
  goodTests = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                              , Map.fromList [(Name "x" 0, 5)] ]
  badTests  = Vector.fromList [ Map.fromList [(Name "x" 0, -1)]
                              , Map.fromList [(Name "x" 0, -5)] ]
  expected  = Lt (Num 0) (Var x)
  task = pie Vector.empty Set.empty goodTests badTests
  in runAndAssertEquivalent expected $ evalStateT task $ PieEnv names lits


--
-- NB: Full LoopInvGen tests are expensive and are thus located in the verification-test suite.
--
