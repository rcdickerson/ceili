{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.InvariantInference.PieTest(htf_thisModulesTests) where

import Test.Framework

import Ceili.InvariantInference.Pie
import qualified Data.Map as Map
import Data.Vector ( Vector )
import qualified Data.Vector as Vector

assertHasSameItems :: (Ord a, Show a) => Vector a -> Vector a -> IO ()
assertHasSameItems expectedVec actualVec = let
  addToCount item counts = let current = Map.findWithDefault 0 item counts
                           in Map.insert item (current + 1) counts
  countItems = Vector.foldr addToCount Map.empty
  in assertEqual (countItems expectedVec) (countItems actualVec)


test_clausesWithSize_0_0 =
  assertEqual (Vector.empty :: Vector Clause) $ clausesWithSize 0 0

test_clausesWithSize_1_0 =
  assertEqual (Vector.empty :: Vector Clause) $ clausesWithSize 1 0

test_clausesWithSize_0_1 =
  assertEqual (Vector.empty :: Vector Clause) $ clausesWithSize 0 1

test_clausesWithSize_5_1 =
  assertEqual (Vector.empty :: Vector Clause) $ clausesWithSize 5 1

test_clausesWithSize_1_1 =
  let expected = Vector.fromList [ Map.singleton 0 CPos
                                 , Map.singleton 0 CNeg ]
  in assertHasSameItems expected $ clausesWithSize 1 1

test_clausesWithSize_1_2 =
  let expected = Vector.fromList [ Map.singleton 0 CPos
                                 , Map.singleton 1 CPos
                                 , Map.singleton 0 CNeg
                                 , Map.singleton 1 CNeg]
  in assertHasSameItems expected $ clausesWithSize 1 2

test_clausesWithSize_2_3 =
  let expected = Vector.fromList [ -- 0, 1 combos
                                   Map.fromAscList [(0, CPos), (1, CPos)]
                                 , Map.fromAscList [(0, CPos), (1, CNeg)]
                                 , Map.fromAscList [(0, CNeg), (1, CPos)]
                                 , Map.fromAscList [(0, CNeg), (1, CNeg)]
                                   -- 0, 2 combos
                                 , Map.fromAscList [(0, CPos), (2, CPos)]
                                 , Map.fromAscList [(0, CPos), (2, CNeg)]
                                 , Map.fromAscList [(0, CNeg), (2, CPos)]
                                 , Map.fromAscList [(0, CNeg), (2, CNeg)]
                                   -- 1, 2 combos
                                 , Map.fromAscList [(1, CPos), (2, CPos)]
                                 , Map.fromAscList [(1, CPos), (2, CNeg)]
                                 , Map.fromAscList [(1, CNeg), (2, CPos)]
                                 , Map.fromAscList [(1, CNeg), (2, CNeg)]
                                 ]
  in assertHasSameItems expected $ clausesWithSize 2 3


test_filterInconsistentClauses_simpleAcceptPos = let
  fv       = Vector.fromList [ Vector.fromList [True, True, True] ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CPos)] ]
  in assertHasSameItems clauses $ filterInconsistentClauses clauses fv

test_filterInconsistentClauses_simpleAcceptNeg = let
  fv       = Vector.fromList [ Vector.fromList [False, False, False] ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CNeg), (1, CNeg)] ]
  in assertHasSameItems clauses $ filterInconsistentClauses clauses fv

test_filterInconsistentClauses_simpleAcceptMixed = let
  fv       = Vector.fromList [ Vector.fromList [True, False, False] ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CNeg)] ]
  in assertHasSameItems clauses $ filterInconsistentClauses clauses fv

test_filterInconsistentClauses_simpleAcceptOneMatch = let
  fv       = Vector.fromList [ Vector.fromList [True, True, True] ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CNeg)] ]
  in assertHasSameItems clauses $ filterInconsistentClauses clauses fv

test_filterInconsistentClauses_simpleRejectNeg = let
  fv       = Vector.fromList [ Vector.fromList [True, True, True] ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CNeg), (1, CNeg)] ]
  in assertHasSameItems Vector.empty $ filterInconsistentClauses clauses fv

test_filterInconsistentClauses_simpleRejectPos = let
  fv       = Vector.fromList [ Vector.fromList [False, False, False] ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CPos)] ]
  in assertHasSameItems Vector.empty $ filterInconsistentClauses clauses fv

test_filterInconsistentClauses_simpleRejectMixed = let
  fv       = Vector.fromList [ Vector.fromList [True, False, False] ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CNeg), (1, CPos)] ]
  in assertHasSameItems Vector.empty $ filterInconsistentClauses clauses fv

test_filterInconsistentClauses = let
  fv       = Vector.fromList [ Vector.fromList [True, False, False]
                             , Vector.fromList [True, True,  False]
                             , Vector.fromList [True, True,  True]
                             ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CPos)]
                             , Map.fromAscList [(1, CNeg), (2, CPos)] -- Conflicts with 2nd FV
                             , Map.fromAscList [(1, CPos), (2, CNeg)]
                             ]
  expected = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CPos)]
                             , Map.fromAscList [(1, CPos), (2, CNeg)]]
  in assertHasSameItems expected $ filterInconsistentClauses clauses fv


test_greedySetCover = let
  clauses  = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CPos)] -- Only falsifies the first FV
                             , Map.fromAscList [(1, CPos), (2, CPos)] -- Falsifies the first two FVs
                             , Map.fromAscList [(0, CNeg), (1, CNeg)] -- Falsifies the last two FVs
                             ]
  fv       = Vector.fromList [ Vector.fromList [False, False, False]
                             , Vector.fromList [True, False, False]
                             , Vector.fromList [True, True,  False]
                             , Vector.fromList [True, True,  True]
                             ]
  -- Min cover is the last two clauses, which are sufficient to falsify
  -- the entire feature vector.
  expected = Vector.fromList [ Map.fromAscList [(1, CPos), (2, CPos)]
                             , Map.fromAscList [(0, CNeg), (1, CNeg)]
                             ]
  in case greedySetCover clauses fv of
       Nothing     -> assertFailure "Expected a cover"
       Just actual -> assertHasSameItems expected actual

test_greedySetCover_noCover = let
  clauses  = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CPos)] -- Only falsifies the first FV
                             , Map.fromAscList [(1, CPos), (2, CPos)] -- Falsifies the first two FVs
                             ]
  fv       = Vector.fromList [ Vector.fromList [False, False, False]
                             , Vector.fromList [True, False, False]
                             , Vector.fromList [True, True,  False]
                             , Vector.fromList [True, True,  True]
                             ]
  -- No clause falsifies all feature vectors.
  in case greedySetCover clauses fv of
       Nothing     -> return () -- pass
       Just actual -> assertFailure $ "Unexpected cover: " ++ show actual
