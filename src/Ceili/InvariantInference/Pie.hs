-- An implementation of PIE / LoopInvGen invariant inference from
-- "Data-driven precondition inference with learned features"
-- Padhi, Saswat, Rahul Sharma, and Todd Millstein
-- ACM SIGPLAN Notices 51.6 (2016): 42-56.
-- http://web.cs.ucla.edu/~todd/research/pldi16.pdf

module Ceili.InvariantInference.Pie
  ( Clause
  , ClauseOccur(..)
  , boolLearn
  , clausesWithSize
  , featureLearn
  , filterInconsistentClauses
  , greedySetCover
  , loopInvGen -- TODO: Everything but loopInvGen is exposed for testing. Create .Internal module?
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import qualified Ceili.InvariantInference.LinearInequalities as LI
import Ceili.Language.BExp
import Ceili.Language.Imp
import Ceili.Name
import Data.Maybe ( isJust )
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Vector ( Vector, (!) )
import qualified Data.Vector as Vector


--------------
-- Features --
--------------
type Feature = Assertion

---------------------
-- Feature Vectors --
---------------------
type FeatureVector = Vector (Vector Bool)

substituteFV :: Vector Assertion -> Assertion -> Assertion
substituteFV = error "unimplemented"

createFV :: Vector Feature -> Vector Test -> Ceili FeatureVector
createFV features tests = Vector.generateM (Vector.length tests) testVec
  where
    testVec n = Vector.generateM (Vector.length features) $ checkFeature (tests!n)
    checkFeature test n = checkValid $ Imp test (features!n)

-----------
-- Tests --
-----------
type Test = Assertion -- TODO: Allow other kinds of tests.


----------------
-- LoopInvGen --
----------------

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


---------
-- PIE --
---------

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


-------------
-- Clauses --
-------------

data ClauseOccur = CPos | CNeg
  deriving (Show, Ord, Eq)
type Clause = Map Int ClauseOccur

clauseToAssertion :: Vector Feature -> Clause -> Assertion
clauseToAssertion features clause = let
  toAssertion (idx, occur) = case occur of
    CPos -> features!idx
    CNeg -> Not $ features!idx
  in case map toAssertion $ Map.toList clause of
       []     -> ATrue
       (a:[]) -> a
       as     -> Or as

clausesToAssertion :: Vector Feature -> [Clause] -> Assertion
clausesToAssertion features clauses =
  case map (clauseToAssertion features) clauses of
    []     -> ATrue
    (a:[]) -> a
    as     -> And as

clausesWithSize :: Int -> Int -> Vector Clause
clausesWithSize size numFeatures =
  if numFeatures < 1 then Vector.empty
  else if size > numFeatures then Vector.empty
  else case size of
    0 -> Vector.empty
    1 -> let
      pos = Vector.fromList $ map (\i -> Map.singleton i CPos) [0..numFeatures-1]
      neg = Vector.fromList $ map (\i -> Map.singleton i CNeg) [0..numFeatures-1]
      in pos Vector.++ neg
    _ -> let
      prev    = clausesWithSize (size - 1) (numFeatures - 1)
      pos     = Vector.map (\clause -> Map.insert (numFeatures - 1) CPos clause) prev
      neg     = Vector.map (\clause -> Map.insert (numFeatures - 1) CNeg clause) prev
      smaller = clausesWithSize size $ numFeatures - 1
      in pos Vector.++ neg Vector.++ smaller

falsifies :: Clause -> Vector Bool -> Bool
falsifies clause vec = and $ map conflicts $ Map.toList clause
  where
    conflicts (i, occur) = case occur of
      CPos -> not $ vec!i
      CNeg -> vec!i


---------------------------------
-- Boolean Expression Learning --
---------------------------------

boolLearn :: Vector Feature -> FeatureVector -> FeatureVector -> Ceili Assertion
boolLearn features posFV negFV = do
  log_i "[PIE] Learning boolean formula"
  boolLearn' features posFV negFV 1 Vector.empty

boolLearn' :: Vector Feature -> FeatureVector -> FeatureVector -> Int -> Vector Clause -> Ceili Assertion
boolLearn' features posFV negFV k prevClauses = do
  log_d $ "[PIE] Boolean learning: looking at clauses up to size " ++ show k ++ "..."
  let nextClauses    = clausesWithSize k $ Vector.length features
  let consistentNext = filterInconsistentClauses nextClauses posFV
  let clauses        = consistentNext Vector.++ prevClauses -- Later we foldr so want to append in descending
                                                            -- clause size order to favor smaller clauses.
                                                            -- TODO: Make this less fragile.
  let mSolution      = greedySetCover clauses negFV
  case mSolution of
    Just solution -> return $ clausesToAssertion features $ Vector.toList solution
    Nothing -> boolLearn' features posFV negFV (k + 1) clauses

filterInconsistentClauses :: Vector Clause -> FeatureVector -> Vector Clause
filterInconsistentClauses clauses fv = Vector.filter consistent clauses
  where consistent clause = not . or $ map (falsifies clause) $ Vector.toList fv

greedySetCover :: Vector Clause -> FeatureVector -> Maybe (Vector Clause)
greedySetCover clauses fv =
  case Vector.length clauses of
    0 -> if Vector.length fv == 0 then (Just clauses) else Nothing
    _ ->
      let
        -- Find the clause that eliminates the most feature vectors.
        step curIdx curClause bestSoFar@(bestCount, _, _, _) = let
          curFv    = Vector.filter (not . falsifies curClause) fv
          curCount = (Vector.length fv) - (Vector.length curFv)
          in if curCount > bestCount
             then (curCount, curIdx, curClause, curFv)
             else bestSoFar
        (elimCount, idx, clause, fv') = Vector.ifoldr step (-1, -1, Map.empty, Vector.empty) clauses
      in
        -- If we didn't eliminate any feature vectors, fail.
        if elimCount < 1 then Nothing
        -- If the best clause eliminates all FVs, return. Otherwise, recurse.
        else case length fv' of
               0 -> Just $ Vector.singleton clause
               _ -> do
                 let clauses' = Vector.ifilter (\i _ -> i /= idx) clauses
                 rest <- greedySetCover clauses' fv'
                 return $ clause `Vector.cons` rest


----------------------
-- Feature Learning --
----------------------

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
      Vector.map (\test -> Imp test $ Not assertion) badTests
  firstThatSeparates assertions =
    case assertions of
      []   -> return Nothing
      a:as -> do
        separates <- checkValid $ And [ acceptsGoods a, rejectsBads a ]
        if separates then (return $ Just a) else firstThatSeparates as
  featureLearn' size = do
    log_d $ "[PIE] Examining features of length " ++ show size
    mFeature <- firstThatSeparates $ Set.toList $ LI.linearInequalities names lits size
    case mFeature of
      Nothing -> if size >= maxFeatureSize then return Nothing else featureLearn' (size + 1)
      Just feature -> return $ Just feature
  in do
    log_d "[PIE] Beginning feature learning pass"
    featureLearn' 1

namesInToInt :: CollectableNames c => c -> Set TypedName
namesInToInt c = let
   names = namesIn c
   in Set.map (\n -> TypedName n Int) names
