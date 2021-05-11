-- An implementation of PIE / LoopInvGen invariant inference from
-- "Data-driven precondition inference with learned features"
-- Padhi, Saswat, Rahul Sharma, and Todd Millstein
-- ACM SIGPLAN Notices 51.6 (2016): 42-56.
-- http://web.cs.ucla.edu/~todd/research/pldi16.pdf

module Ceili.InvariantInference.Pie
  (
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.InvariantInference.LinearInequalities
import Ceili.Language.Imp
import Ceili.Name
import Data.Maybe ( isJust )
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.Vector ( Vector, (!) )
import qualified Data.Vector as Vector

type FeatureVector = Vector (Vector Bool)
type Test = Assertion -- TODO: Allow other kinds of tests.

preGen :: ImpProgram -> Assertion -> [Assertion] -> Ceili (Maybe Assertion)
preGen program post tests = do
  (goodTests, badTests) <- partitionTests program post tests
  pie Vector.empty goodTests badTests

partitionTests :: ImpProgram -> Assertion -> [Test] -> Ceili (Vector Test, Vector Test)
partitionTests program post tests = do
  let tagValid test = do
        sp <- forwardPT test program      -- TODO: This could get bogged down in more invar inference.
        valid <- checkValid $ Imp sp post --       Replace with actual evaluation semantics?
        return (test, valid)
  tagged <- Vector.mapM tagValid $ Vector.fromList tests
  let (good, bad) = Vector.unstablePartition snd tagged
  return (Vector.map fst good, Vector.map fst bad)

pie :: Vector Assertion -> Vector Test -> Vector Test -> Ceili (Maybe Assertion)
pie features goodTests badTests = do
  posFV <- createFV features goodTests
  negFV <- createFV features badTests
  case (getConflict posFV negFV goodTests badTests) of
    Just (xGood, xBad) -> do
      let maxDepth = 3 -- TODO: Don't hardcode max depth
      mNewFeature <- featureLearn maxDepth xGood xBad
      case mNewFeature of
        Just newFeature -> do
          log_d $ "[PIE] Learned new feature: " ++ show newFeature
          pie (Vector.cons newFeature features) goodTests badTests
        Nothing -> do
          log_e $ "[PIE] Unable to find separating feature (at max depth " ++ show maxDepth ++ ")"
          return Nothing
    Nothing -> do
      classifier <- boolLearn posFV negFV
      return $ Just $ substituteFV features classifier

createFV :: Vector Assertion -> Vector Test -> Ceili FeatureVector
createFV features tests = Vector.generateM (Vector.length tests) testVec
  where
    testVec n = Vector.generateM (Vector.length features) $ checkFeature (tests!n)
    checkFeature test n = checkValid $ Imp test (features!n)

getConflict :: FeatureVector
            -> FeatureVector
            -> Vector Test
            -> Vector Test
            -> Maybe (Vector Test, Vector Test)
getConflict posFV negFV goodTests badTests = do
  conflict <- findConflict posFV negFV
  let posIndices = Vector.findIndices (== conflict) posFV
  let negIndices = Vector.findIndices (== conflict) negFV
  return (Vector.backpermute goodTests posIndices, Vector.backpermute badTests negIndices)

findConflict :: FeatureVector -> FeatureVector -> Maybe (Vector Bool)
findConflict posFV negFV = Vector.find (\pos -> isJust $ Vector.find (== pos) negFV) posFV

boolLearn :: FeatureVector -> FeatureVector -> Ceili Assertion
boolLearn = error "unimplemented"

substituteFV :: Vector Assertion -> Assertion -> Assertion
substituteFV = error "unimplemented"

featureLearn :: Int -> Vector Test -> Vector Test -> Ceili (Maybe Assertion)
featureLearn maxFeatureSize goodTests badTests = let
  -- TODO: really need names / lits from the whole program?
  names = Set.union (namesInToInt $ Vector.toList goodTests)
                    (namesInToInt $ Vector.toList badTests)
  lits = Set.empty
  acceptsGoods assertion = And $ Vector.toList $
      Vector.map (\test -> Imp test assertion) goodTests
  rejectsBads assertion = And $ Vector.toList $
      Vector.map (\test -> Not $ Imp test assertion) goodTests
  firstToSeparate assertions =
    case assertions of
      []   -> return Nothing
      a:as -> do
        separates <- checkValid $ And [ acceptsGoods a, rejectsBads a ]
        if separates then (return $ Just a) else firstToSeparate as
  featureLearn' size = do
    log_d $ "[PIE] Examining features of length " ++ show size
    mfeature <- firstToSeparate $ Set.toList $ linearInequalities names lits size
    case mfeature of
      Nothing -> if size >= maxFeatureSize then return Nothing else featureLearn' (size + 1)
      Just feature -> return $ Just feature
  in do
    log_d "[PIE] Beginning feature learning pass"
    featureLearn' 1

namesInToInt :: CollectableNames c => c -> Set TypedName
namesInToInt c = let
   names = namesIn c
   in Set.map (\n -> TypedName n Int) names
