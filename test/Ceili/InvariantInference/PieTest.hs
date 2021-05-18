{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.InvariantInference.PieTest(htf_thisModulesTests) where

import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.InvariantInference.Pie
import Ceili.Language.Imp
import Ceili.Name
import qualified Ceili.SMT as SMT
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Vector ( Vector )
import qualified Data.Vector as Vector
import System.Log.FastLogger

assertHasSameItems :: (Ord a, Show a) => Vector a -> Vector a -> IO ()
assertHasSameItems expectedVec actualVec = let
  addToCount item counts = let current = Map.findWithDefault 0 item counts
                           in Map.insert item (current + 1) counts
  countItems = Vector.foldr addToCount Map.empty
  in assertEqual (countItems expectedVec) (countItems actualVec)

assertEquivalent :: Assertion -> Assertion -> IO ()
assertEquivalent a1 a2 = do
  let iff = And [ Imp a1 a2, Imp a2 a1 ]
  result <- withFastLogger LogNone $ \logger ->
            SMT.checkValidFL logger iff
  case result of
    SMT.Valid        -> return () -- pass
    SMT.Invalid s    -> assertFailure s
    SMT.ValidUnknown -> assertFailure "Unable to establish equivalence."

runAndAssertEquivalent :: Assertion -> Ceili (Maybe Assertion) -> IO ()
runAndAssertEquivalent expected actual = do
  result <- runCeili defaultEnv actual
  case result of
    Left err         -> assertFailure err
    Right mAssertion ->
      case mAssertion of
        Nothing     -> assertFailure "Expected assertion, got Nothing."
        Just actual -> assertEquivalent expected actual


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


test_boolLearn = let
  x        = Var $ TypedName (Name "x" 0) Int
  features = Vector.fromList [ Lt x (Num 0)
                             , Lt (Num 0) x
                             , Lt (Num 1) x
                             , Lt x (Num 5)
                             , Lt x (Num 10) ]
  -- Target: 0 < x < 5
  posFV    = Vector.fromList [ Vector.fromList [False, True,  False, True,  True] -- x = 1
                             , Vector.fromList [False, True,  True,  True,  True] -- x = 2
                             ]
  negFV    = Vector.fromList [ Vector.fromList [True,  False, False, True,  True] -- x = -1
                             , Vector.fromList [False, False, False, True,  True] -- x = 0
                             , Vector.fromList [False, True,  True,  False, True] -- x = 7
                             ]
  expected = And [ Lt (Num 0) x, Lt x (Num 5)]
  in do
    result <- runCeili defaultEnv $ boolLearn features posFV negFV
    case result of
      Left err     -> assertFailure err
      Right actual -> assertEqual expected actual

test_boolLearn_largerClause = let
  x        = Var $ TypedName (Name "x" 0) Int
  features = Vector.fromList [ Lt x (Num 0)
                             , Lt (Num 0) x
                             , Lt (Num 1) x
                             , Lt x (Num 5)
                             , Lt x (Num 10)
                             , Eq x (Num 10)
                             , Eq x (Num 7)
                             ]
  -- Target: (x < 5  or  x >= 10  or  x = 7)  and  (x >= 0)
  posFV    = Vector.fromList [ Vector.fromList [False, False, False, True,  True,  False, False] -- x = 0
                             , Vector.fromList [False, True,  False, True,  True,  False, False] -- x = 1
                             , Vector.fromList [False, True,  True,  True,  True,  False, False] -- x = 2
                             , Vector.fromList [False, True,  True,  False, True,  False, True]  -- x = 7
                             , Vector.fromList [False, True,  True,  False, False, True,  False] -- x = 10
                             , Vector.fromList [False, True,  True,  False, False, False, False] -- x = 11
                             ]
  negFV    = Vector.fromList [ Vector.fromList [True,  False, False, True,  True,  False, False] -- x = -1
                             , Vector.fromList [False, True,  True,  False, True,  False, False] -- x = 6
                             , Vector.fromList [False, True,  True,  False, True,  False, False] -- x = 9

                             ]
  expected = And [ Or [ Lt x (Num 5)
                      , Not $ Lt x (Num 10)
                      , Eq x (Num 7)
                      ]
                 , Not $ Lt x (Num 0)
                 ]
  in do
    result <- runCeili defaultEnv $ boolLearn features posFV negFV
    case result of
      Left err     -> assertFailure err
      Right actual -> assertEqual expected actual


test_featureLearn = let
  x         = TypedName (Name "x" 0) Int
  names     = Set.singleton x
  lits      = Set.empty
  goodTests = Vector.fromList [ Eq (Var x) (Num 1)
                              , Eq (Var x) (Num 5) ]
  badTests  = Vector.fromList [ Eq (Var x) (Num $ -1)
                              , Eq (Var x) (Num $ -5) ]
  expected  = Lt (Num 0) (Var x)
  in runAndAssertEquivalent expected $ featureLearn names lits 1 goodTests badTests


test_pie = let
  x         = TypedName (Name "x" 0) Int
  names     = Set.singleton x
  lits      = Set.empty
  goodTests = Vector.fromList [ Eq (Var x) (Num 1)
                              , Eq (Var x) (Num 5) ]
  badTests  = Vector.fromList [ Eq (Var x) (Num $ -1)
                              , Eq (Var x) (Num $ -5) ]
  expected  = Lt (Num 0) (Var x)
  in runAndAssertEquivalent expected $ pie names lits Vector.empty goodTests badTests


-- This is the "Slow Subtraction" example from Software Foundations, Pierce et al.
-- https://softwarefoundations.cis.upenn.edu/plf-current/Hoare2.html
test_loopInvGen = let
  x = Name "x" 0
  y = Name "y" 0
  n = Name "n" 0
  m = Name "m" 0
  tn n = TypedName n Int
  var n = Var $ tn n
  cond = BNe (AVar x) (ALit 0)
  body = impSeq [ impAsgn y $ ASub (AVar y) (ALit 1)
                , impAsgn x $ ASub (AVar x) (ALit 1)]
  post = Imp (And [ Gte (var m) (Num 0)
                  , Gte (var n) (Num 0) ])
             (Eq (var y)
                 (Sub [var n, var m]))
  -- Loop will always start in a state where x = m and y = n.
  tests = [ And [ Eq (var x) (Num 0)
                , Eq (var y) (Num 0)
                , Eq (var m) (Num 0)
                , Eq (var n) (Num 0)]
          , And [ Eq (var x) (Num 5)
                , Eq (var y) (Num 3)
                , Eq (var m) (Num 5)
                , Eq (var n) (Num 3)]
          , And [ Eq (var x) (Num 3)
                , Eq (var y) (Num 5)
                , Eq (var m) (Num 3)
                , Eq (var n) (Num 5)]
          ]
  expected = Eq (Sub [var y, var x])
                (Sub [var n, var m])
  in runAndAssertEquivalent expected $ loopInvGen cond body post tests