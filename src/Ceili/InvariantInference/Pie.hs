-- An implementation of PIE / LoopInvGen invariant inference from
-- "Data-driven precondition inference with learned features"
-- Padhi, Saswat, Rahul Sharma, and Todd Millstein
-- ACM SIGPLAN Notices 51.6 (2016): 42-56.
-- http://web.cs.ucla.edu/~todd/research/pldi16.pdf

module Ceili.InvariantInference.Pie
  ( loopInvGen
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.InvariantInference.LinearInequalities
import Ceili.Language.BExp
import Ceili.Language.Imp
import Ceili.Name
import Data.Maybe ( isJust )
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.Vector ( Vector, (!) )
import qualified Data.Vector as Vector

type Feature = Assertion
type FeatureVector = Vector (Vector Bool)
type Test = Assertion -- TODO: Allow other kinds of tests.

loopInvGen :: BExp
           -> ImpProgram
           -> Assertion
           -> [Test]
           -> Ceili (Maybe Assertion)
loopInvGen cond body post goodTests = do
  let condA = bexpToAssertion cond
  mInvar <- vPreGen (Not condA)
                    impSkip
                    post
                    (Vector.fromList goodTests)
                    Vector.empty
  case mInvar of
    Nothing -> return Nothing
    Just invar -> do
      let makeInductive invar = do
            sp <- forwardPT (And [invar, condA]) body
            inductive <- checkValid $ Imp sp invar
            case inductive of
              True -> return $ Just invar
              False -> do
                mInvar' <- vPreGen (And [invar, condA])
                                  body
                                  invar
                                  (Vector.fromList goodTests)
                                  Vector.empty
                case mInvar' of
                  Nothing -> return Nothing
                  Just invar' -> makeInductive $ And [invar, invar']
      mInvar' <- makeInductive invar
      case mInvar' of
        Nothing -> return Nothing
        Just invar' -> do
          mCounter <- findCounterexample $ invar'
          case mCounter of
            Nothing -> return $ Just invar'
            Just counter -> loopInvGen cond body post (counter:goodTests)

vPreGen :: Assertion
        -> ImpProgram
        -> Assertion
        -> Vector Test
        -> Vector Test
        -> Ceili (Maybe Assertion)
vPreGen pre program post goodTests badTests = do
  let names = namesInToInt program
  let lits = Set.empty -- TODO: Lits
  mCandidate <- pie names lits Vector.empty goodTests badTests
  case mCandidate of
    Nothing -> return Nothing
    Just candidate -> do
      sp <- forwardPT (And [candidate, pre]) program
      mCounter <- findCounterexample $ Imp sp post
      case mCounter of
        Nothing -> return $ Just candidate
        Just counter -> vPreGen pre program post goodTests $
          Vector.cons counter badTests

-- partitionTests :: ImpProgram -> Assertion -> [Test] -> Ceili (Vector Test, Vector Test)
-- partitionTests program post tests = do
--   let tagValid test = do
--         sp <- forwardPT test program      -- TODO: This could get bogged down in more invar inference.
--         valid <- checkValid $ Imp sp post --       Replace with actual evaluation semantics?
--         return (test, valid)
--   tagged <- Vector.mapM tagValid $ Vector.fromList tests
--   let (good, bad) = Vector.unstablePartition snd tagged
--   return (Vector.map fst good, Vector.map fst bad)

pie :: Set TypedName
    -> Set Integer
    -> Vector Feature
    -> Vector Test
    -> Vector Test
    -> Ceili (Maybe Assertion)
pie names lits features goodTests badTests = do
  posFV <- createFV features goodTests
  negFV <- createFV features badTests
  case (getConflict posFV negFV goodTests badTests) of
    Just (xGood, xBad) -> do
      let maxDepth = 3 -- TODO: Don't hardcode max depth
      mNewFeature <- featureLearn names lits maxDepth xGood xBad
      case mNewFeature of
        Just newFeature -> do
          log_d $ "[PIE] Learned new feature: " ++ show newFeature
          pie names lits (Vector.cons newFeature features) goodTests badTests
        Nothing -> do
          log_e $ "[PIE] Unable to find separating feature (at max depth " ++ show maxDepth ++ ")"
          return Nothing
    Nothing -> do
      classifier <- boolLearn features posFV negFV
      return $ Just $ substituteFV features classifier

createFV :: Vector Feature -> Vector Test -> Ceili FeatureVector
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

boolLearn :: Vector Feature -> FeatureVector -> FeatureVector -> Ceili Assertion
boolLearn features posFV negFV = do
  log_i "[PIE] Learning boolean formula"
  boolLearn' features posFV negFV 1 Vector.empty

boolLearn' :: Vector Feature -> FeatureVector -> FeatureVector -> Int -> Vector Assertion -> Ceili Assertion
boolLearn' features posFV negFV k prevClauses = do
  log_d $ "[PIE] Boolean learning: looking at clauses up to size " ++ show k ++ "..."
  let nextClauses = clausesWithSize k features
  consistentNext <- filterInconsistentClauses nextClauses posFV
  let clauses     = prevClauses Vector.++ consistentNext
  mSolution      <- greedySetCover clauses negFV
  case mSolution of
    Just solution -> return solution
    Nothing -> boolLearn' features posFV negFV (k + 1) clauses

clausesWithSize :: Int -> Vector Feature -> Vector Assertion
clausesWithSize size features =
  if (size < 1) then error ("Clause size must be at least 1, was: " ++ show size) else
    case (Vector.length features) of
      0       -> Vector.empty
      fLength ->
        error "unimplemented"

filterInconsistentClauses :: Vector Assertion -> FeatureVector -> Ceili (Vector Assertion)
filterInconsistentClauses clauses fv = do
  error "unimplemented"

greedySetCover :: Vector Assertion -> FeatureVector -> Ceili (Maybe Assertion)
greedySetCover features fv = do
  error "unimplemented"

substituteFV :: Vector Assertion -> Assertion -> Assertion
substituteFV = error "unimplemented"

featureLearn :: Set TypedName
             -> Set Integer
             -> Int
             -> Vector Test
             -> Vector Test
             -> Ceili (Maybe Assertion)
featureLearn names lits maxFeatureSize goodTests badTests = let
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
