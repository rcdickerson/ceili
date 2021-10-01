{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Ceili.InvariantInference.PieTest(htf_thisModulesTests) where

import Ceili.TestUtil
import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.InvariantInference.Pie
import Ceili.Name
import Ceili.SMTString
import Control.Monad.Trans.State ( evalStateT )
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Vector as Vector

runAndAssertEquivalent :: (SMTString t, SMTTypeString t, ValidCheckable t)
                       => Assertion t -> Ceili (Maybe (Assertion t)) -> IO ()
runAndAssertEquivalent expected actual = do
  result <- runCeili emptyEnv actual
  case result of
    Left err         -> assertFailure err
    Right mAssertion ->
      case mAssertion of
        Nothing        -> assertFailure "Expected assertion, got Nothing."
        Just assertion -> assertEquivalent expected assertion


test_createFV = let
  x = Var $ Name "x" 0
  assertions = Vector.fromList [Eq @Integer x (Num 0), Lt x (Num 3), Lte x (Num 3)]
  states = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                           , Map.fromList [(Name "x" 0, 2)]
                           , Map.fromList [(Name "x" 0, 3)]
                           ]
  expected = Vector.fromList [ Vector.fromList [True,  True,  True]
                             , Vector.fromList [False, True,  True]
                             , Vector.fromList [False, False, True]
                             ]
  in do
    result <- runCeili emptyEnv $ createFV assertions states
    case result of
      Left err     -> assertFailure err
      Right actual -> assertEqual expected actual

test_getConflict_noConflicts = let
  posFVs = Vector.fromList [ Vector.fromList [True, True,  False]
                           , Vector.fromList [True, True,  False]
                           , Vector.fromList [True, False, True]
                           ]
  negFVs = Vector.fromList [ Vector.fromList [False, False, True]
                           , Vector.fromList [True,  False, False]
                           , Vector.fromList [False, False, True]
                           ]
  goodTests = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                              , Map.fromList [(Name "x" 0, 2)]
                              , Map.fromList [(Name "x" 0, 4)]
                              ]
  badTests = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                             , Map.fromList [(Name "x" 0, 3)]
                             , Map.fromList [(Name "x" 0, 5)]
                             ]
  in assertEqual Nothing $ getConflict posFVs negFVs goodTests badTests

test_getConflict_oneConflict = let
  posFVs = Vector.fromList [ Vector.fromList [True, False, True]
                           , Vector.fromList [True, True,  False]
                           , Vector.fromList [True, False, True]
                           ]
  negFVs = Vector.fromList [ Vector.fromList [False, False, True]
                           , Vector.fromList [True,  False, False]
                           , Vector.fromList [True,  True,  False]
                           ]
  goodTests = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                              , Map.fromList [(Name "x" 0, 2)]
                              , Map.fromList [(Name "x" 0, 4)]
                              ]
  badTests = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                             , Map.fromList [(Name "x" 0, 3)]
                             , Map.fromList [(Name "x" 0, 5)]
                             ]
  expectedXGood = Vector.fromList [ Map.fromList [(Name "x" 0, 2)] ]
  expectedXBad = Vector.fromList [ Map.fromList [(Name "x" 0, 5)] ]
  expected = Just (expectedXGood, expectedXBad)
  in assertEqual expected $ getConflict posFVs negFVs goodTests badTests

test_getConflict_twoGoodConflicts = let
  posFVs = Vector.fromList [ Vector.fromList [True, True,  False]
                           , Vector.fromList [True, True,  False]
                           , Vector.fromList [True, False, True]
                           ]
  negFVs = Vector.fromList [ Vector.fromList [False, False, True]
                           , Vector.fromList [True,  True, False]
                           , Vector.fromList [False, False, True]
                           ]
  goodTests = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                              , Map.fromList [(Name "x" 0, 2)]
                              , Map.fromList [(Name "x" 0, 4)]
                              ]
  badTests = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                             , Map.fromList [(Name "x" 0, 3)]
                             , Map.fromList [(Name "x" 0, 5)]
                             ]
  expectedXGood = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                                  , Map.fromList [(Name "x" 0, 2)]
                                  ]
  expectedXBad = Vector.fromList [ Map.fromList [(Name "x" 0, 3)] ]
  expected = Just (expectedXGood, expectedXBad)
  in assertEqual expected $ getConflict posFVs negFVs goodTests badTests

test_getConflict_twoBadConflicts = let
  posFVs = Vector.fromList [ Vector.fromList [True, True,  False]
                           , Vector.fromList [True, False, False]
                           , Vector.fromList [True, False, True]
                           ]
  negFVs = Vector.fromList [ Vector.fromList [True,  True, False]
                           , Vector.fromList [True,  True, False]
                           , Vector.fromList [False, False, True]
                           ]
  goodTests = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                              , Map.fromList [(Name "x" 0, 2)]
                              , Map.fromList [(Name "x" 0, 4)]
                              ]
  badTests = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                             , Map.fromList [(Name "x" 0, 3)]
                             , Map.fromList [(Name "x" 0, 5)]
                             ]
  expectedXGood = Vector.fromList [ Map.fromList [(Name "x" 0, 0)] ]
  expectedXBad = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                                 , Map.fromList [(Name "x" 0, 3)]
                                 ]
  expected = Just (expectedXGood, expectedXBad)
  in assertEqual expected $ getConflict posFVs negFVs goodTests badTests

test_getConflict_twoConflictsEach = let
  posFVs = Vector.fromList [ Vector.fromList [True, True,  False]
                           , Vector.fromList [True, True,  False]
                           , Vector.fromList [True, False, True]
                           ]
  negFVs = Vector.fromList [ Vector.fromList [False, False, True]
                           , Vector.fromList [True,  True, False]
                           , Vector.fromList [True,  True, False]
                           ]
  goodTests = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                              , Map.fromList [(Name "x" 0, 2)]
                              , Map.fromList [(Name "x" 0, 4)]
                              ]
  badTests = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                             , Map.fromList [(Name "x" 0, 3)]
                             , Map.fromList [(Name "x" 0, 5)]
                             ]
  expectedXGood = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                                  , Map.fromList [(Name "x" 0, 2)]
                                  ]
  expectedXBad = Vector.fromList [ Map.fromList [(Name "x" 0, 3)]
                                 , Map.fromList [(Name "x" 0, 5)]
                                 ]
  expected = Just (expectedXGood, expectedXBad)
  in assertEqual expected $ getConflict posFVs negFVs goodTests badTests

test_getConflict_twoPossibleAnswers = let
  posFVs = Vector.fromList [ Vector.fromList [True, True,  False]
                           , Vector.fromList [True, False, False]
                           , Vector.fromList [True, False, True]
                           ]
  negFVs = Vector.fromList [ Vector.fromList [False, False, True]
                           , Vector.fromList [True,  True,  False]
                           , Vector.fromList [True, False, True]
                           ]
  goodTests = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                              , Map.fromList [(Name "x" 0, 2)]
                              , Map.fromList [(Name "x" 0, 4)]
                              ]
  badTests = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                             , Map.fromList [(Name "x" 0, 3)]
                             , Map.fromList [(Name "x" 0, 5)]
                             ]
  expectedXGood = Vector.fromList [ Map.fromList [(Name "x" 0, 0)] ]
  expectedXBad = Vector.fromList [ Map.fromList [(Name "x" 0, 3)] ]
  expected = Just (expectedXGood, expectedXBad)
  in assertEqual expected $ getConflict posFVs negFVs goodTests badTests

test_pie = let
  x         = Name "x" 0
  names     = Set.singleton x
  lits      = Set.empty
  goodTests = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                              , Map.fromList [(Name "x" 0, 5)] ]
  badTests  = Vector.fromList [ Map.fromList [(Name "x" 0, -1)]
                              , Map.fromList [(Name "x" 0, -5)] ]
  expected  = Lt @Integer (Num 0) (Var x)
  task = pie Vector.empty goodTests badTests
  in runAndAssertEquivalent expected $ evalStateT task $ mkPieEnv names lits []


--
-- NB: Full LoopInvGen tests are expensive and are thus located in the verification-test suite.
--
