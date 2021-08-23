module Ceili.FeatureLearning.PACBoolean
  ( Clause
  , ClauseOccur(..)
  , clausesWithSize
  , filterInconsistentClauses
  , greedySetCover
  , learnBoolExpr
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.SMTString
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Vector ( Vector, (!) )
import qualified Data.Vector as Vector


type FeatureVector = Vector (Vector Bool)

learnBoolExpr :: Vector Assertion -> FeatureVector -> FeatureVector -> Ceili Assertion
learnBoolExpr features posFV negFV = do
  log_d "[PAC] Begin learning boolean expression..."
  boolLearn features posFV negFV 1 Vector.empty

boolLearn :: Vector Assertion
          -> FeatureVector
          -> FeatureVector
          -> Int
          -> Vector Clause
          -> Ceili Assertion
boolLearn features posFV negFV k prevClauses = do
  log_d $ "[PAC] Loking at clauses of size " ++ show k
  let nextClauses    = clausesWithSize k $ Vector.length features
  let consistentNext = filterInconsistentClauses nextClauses posFV
  let clauses        = consistentNext Vector.++ prevClauses
  let mSolution      = greedySetCover clauses negFV
  case mSolution of
    Just solution -> do
      let assertion = clausesToAssertion features $ Vector.toList solution
      log_d $ "[PAC] Learned boolean expression: " ++ (showSMT assertion)
      return $ assertion
    Nothing -> boolLearn features posFV negFV (k + 1) clauses

filterInconsistentClauses :: Vector Clause -> FeatureVector -> Vector Clause
filterInconsistentClauses clauses fv = Vector.filter consistent clauses
  where consistent clause = not . or $ map (falsifies clause) $ Vector.toList fv

falsifies :: Clause -> Vector Bool -> Bool
falsifies clause vec = and $ map conflicts $ Map.toList clause
  where
    conflicts (i, occur) = case occur of
      CPos -> not $ vec!i
      CNeg -> vec!i

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


----------------------------------
-- Sparse Clause Representation --
----------------------------------

data ClauseOccur = CPos | CNeg
  deriving (Show, Ord, Eq)
type Clause = Map Int ClauseOccur

clauseToAssertion :: Vector Assertion -> Clause -> Assertion
clauseToAssertion features clause = let
  toAssertion (idx, occur) = case occur of
    CPos -> features!idx
    CNeg -> Not $ features!idx
  in case map toAssertion $ Map.toList clause of
       []     -> ATrue
       (a:[]) -> a
       as     -> Or as

clausesToAssertion :: Vector Assertion -> [Clause] -> Assertion
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
