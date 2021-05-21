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
  , pie
  , greedySetCover
  , loopInvGen -- TODO: Everything but loopInvGen is exposed for testing. Create .Internal module?
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import qualified Ceili.InvariantInference.LinearInequalities as LI
import Ceili.Language.BExp
import Ceili.Language.Imp
import Ceili.Name
import Ceili.SMTString ( showSMT )
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
  log_i $ "[PIE] Beginning invariant learning"
  log_i $ "[PIE] LoopInvGen searching for initial candidate invariant..."
  let condA = bexpToAssertion cond
  mInvar <- vPreGen (Not condA)
                    impSkip
                    post
                    (Vector.fromList goodTests)
                    Vector.empty
  log_i $ "[PIE] LoopInvGen initial invariant: " ++ (showSMT mInvar)
  case mInvar of
    Nothing -> return Nothing
    Just invar -> do
      let makeInductive invar = do
            sp <- forwardPT (And [invar, condA]) body
            inductive <- checkValid $ Imp sp invar
            case inductive of
              True -> return $ Just invar
              False -> do
                log_i $ "[PIE] LoopInvGen invariant not inductive, attempting to strengthen..."
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
         Nothing -> log_i "[PIE] LoopInvGen unable to find inductive strengthening of invariant"
                    >> return Nothing
         Just invar' -> do
           log_i $ "[PIE] LoopInvGen strengthened (inductive) invariant: " ++ (showSMT mInvar')
           log_i $ "[PIE] Attempting to weaken invariant..."
           let validInvar inv = do
                 sp <- forwardPT (And [condA, inv]) body
                 checkValid $ And [ Imp (And [Not condA, inv]) post
                                  , Imp sp  inv ]
           weakenedInvar <- weaken validInvar invar'
           log_i $ "[PIE] Learned invariant: " ++ showSMT weakenedInvar
           return $ Just weakenedInvar
      -- The PIE paper now looks for a contradiction with the precond and then weakens
      -- the invariant if needed. We don't have a precond in the case where we are
      -- looking for a WP in our PTS, so leave this off for now. (Instead, we do a Pareto
      -- optimality weakening by iteratively removing clauses unneeded to establish the
      -- invariant / post -- see `weaken` below.)
      -- mCounter <- findCounterexample $ Imp precond invar'
      -- case mCounter of
      --    Nothing -> return $ Just invar'
      --    Just counter -> do
      --      log_d $ "[PIE] LoopInvGen found counterexample to strengthened invariant: "
      --            ++ (showSMT counter)
      --      loopInvGen cond body post (counter:goodTests)

weaken :: (Assertion -> Ceili Bool) -> Assertion -> Ceili Assertion
weaken sufficient assertion = do
  let conj = conjuncts assertion
  conj' <- paretoOptimize (sufficient . And) conj
  return $ case conj' of
             []     -> ATrue
             (a:[]) -> a
             as     -> And as

conjuncts :: Assertion -> [Assertion]
conjuncts assertion = case assertion of
  And as -> concat $ map conjuncts as
  _      -> [assertion]

paretoOptimize :: ([Assertion] -> Ceili Bool) -> [Assertion] -> Ceili [Assertion]
paretoOptimize sufficient assertions =
  let
    optimize (needed, toExamine) =
      case toExamine of
        []     -> return $ needed
        (a:as) -> do
          worksWithoutA <- sufficient (needed ++ as)
          if worksWithoutA
            then optimize (needed, as)
            else optimize (a:needed, as)
  in optimize ([], assertions)

vPreGen :: Assertion
        -> ImpProgram
        -> Assertion
        -> Vector Test
        -> Vector Test
        -> Ceili (Maybe Assertion)
vPreGen pre program post goodTests badTests = do
  log_d $ "[PIE] Starting vPreGen pass"
  log_d $ "[PIE]   pre: " ++ showSMT pre
  log_d $ "[PIE]   post: " ++ showSMT post
  log_d $ "[PIE]   Good tests: " ++ (show $ Vector.map showSMT goodTests)
  log_d $ "[PIE]   Bad tests: " ++ (show $ Vector.map showSMT badTests)
  let names = Set.unions $ Vector.toList $
        (Vector.singleton $ namesInToInt program) Vector.++
        (Vector.map namesInToInt goodTests) Vector.++
        (Vector.map namesInToInt badTests)
  let lits = Set.empty -- TODO: Lits
  wp <- backwardPT post program
  mCandidate <- pie names lits Vector.empty goodTests badTests
  case mCandidate of
    Nothing -> return Nothing
    Just candidate -> do
      log_d $ "[PIE] vPreGen candidate precondition: " ++ showSMT candidate
      mCounter <- findCounterexample $ Imp (And [candidate, pre]) wp
      case mCounter of
        Nothing -> do
          log_d $ "[PIE] vPreGen found satisfactory precondition: " ++ showSMT candidate
          return $ Just candidate
        Just counter -> do
          log_d $ "[PIE] vPreGen found counterexample: " ++ showSMT counter
          vPreGen pre program post goodTests $ Vector.cons counter badTests


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
  case getConflict posFV negFV goodTests badTests of
    Just (xGood, xBad) -> do
      mNewFeature <- findAugmentingFeature names lits xGood xBad
      case mNewFeature of
        Nothing         -> return Nothing
        Just newFeature -> pie names lits (Vector.cons newFeature features) goodTests badTests
    Nothing -> boolLearn features posFV negFV >>= return . Just

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

findAugmentingFeature :: Set TypedName
                      -> Set Integer
                      -> Vector Test
                      -> Vector Test
                      -> Ceili (Maybe Assertion)
findAugmentingFeature names lits xGood xBad = do
  let maxFeatureSize = 4 -- TODO: Don't hardcode max feature size
  mNewFeature <- featureLearn names lits maxFeatureSize xGood xBad
  case mNewFeature of
    Just newFeature -> do
      return $ Just newFeature
    Nothing -> do
      case (Vector.length xGood, Vector.length xBad) of
        (1, 1) -> log_d "[PIE] Single conflict has no separating feature, giving up"
                  >> return Nothing
        (_, 1) -> log_d "[PIE] Reducing conflict set in good tests" >>
                  findAugmentingFeature names lits (Vector.drop 1 xGood) xBad
        _      -> log_d "[PIE] Reducing conflict set in bad tests" >>
                  findAugmentingFeature names lits xGood (Vector.drop 1 xBad)

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
  log_d "[PIE] Learning boolean formula"
  boolLearn' features posFV negFV 1 Vector.empty

boolLearn' :: Vector Feature -> FeatureVector -> FeatureVector -> Int -> Vector Clause -> Ceili Assertion
boolLearn' features posFV negFV k prevClauses = do
  log_d $ "[PIE] Boolean learning: looking at clauses up to size " ++ show k ++ "..."
  let nextClauses    = clausesWithSize k $ Vector.length features
  let consistentNext = filterInconsistentClauses nextClauses posFV
  let clauses        = consistentNext Vector.++ prevClauses
  let mSolution      = greedySetCover clauses negFV
  case mSolution of
    Just solution -> do
      let assertion = clausesToAssertion features $ Vector.toList solution
      log_d $ "[PIE] Learned boolean expression: " ++ (showSMT assertion)
      return $ assertion
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
        separates <- checkValidWithLog LogLevelNone $ And [ acceptsGoods a, rejectsBads a ]
        if separates then (return $ Just a) else firstThatSeparates as
  featureLearn' size = do
    log_d $ "[PIE] Examining features of length " ++ show size
    mFeature <- firstThatSeparates $ Set.toList $ LI.linearInequalities names lits size
    case mFeature of
      Nothing -> if size >= maxFeatureSize then return Nothing else featureLearn' (size + 1)
      Just feature -> return $ Just feature
  in do
    log_d   "[PIE] Beginning feature learning pass"
    log_d $ "[PIE]   Names: " ++ (show $ Set.map showSMT names)
    log_d $ "[PIE]   Lits: " ++ show lits
    log_d $ "[PIE]   Good tests: " ++ (show $ Vector.map showSMT goodTests)
    log_d $ "[PIE]   Bad tests: " ++ (show $ Vector.map showSMT badTests)
    featureLearn' 1

namesInToInt :: CollectableNames c => c -> Set TypedName
namesInToInt c = let
   names = namesIn c
   in Set.map (\n -> TypedName n Int) names
