{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- An implementation of PIE / LoopInvGen invariant inference from
-- "Data-driven precondition inference with learned features"
-- Padhi, Saswat, Rahul Sharma, and Todd Millstein
-- ACM SIGPLAN Notices 51.6 (2016): 42-56.
-- http://web.cs.ucla.edu/~todd/research/pldi16.pdf

module Ceili.InvariantInference.Pie
  ( CandidateFilter
  , FeatureVector
  , Embeddable(..)
  , PieEnv(..)
  , createFV
  , getConflict
  , pie
  , loopInvGen
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Embedding
import qualified Ceili.FeatureLearning.LinearInequalities as LI
import qualified Ceili.FeatureLearning.PACBoolean as BL
import qualified Ceili.FeatureLearning.Separator as SL
import Ceili.PTS ( BackwardPT )
import Ceili.ProgState
import qualified Ceili.SMT as SMT
import Ceili.StatePredicate
import Control.Monad ( filterM )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State ( StateT, evalStateT, get, put )
import Data.Maybe ( isJust )
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Vector ( Vector, (!) )
import qualified Data.Vector as Vector
import Prettyprinter


---------------------
-- Feature Vectors --
---------------------
type FeatureVector = Vector Bool

createFV :: StatePredicate (Assertion t) t
         => Vector (Assertion t)
         -> Vector (ProgState t)
         -> Ceili (Vector FeatureVector)
createFV features tests =
  let fv = Vector.generate (Vector.length tests) $ \testIdx ->
           Vector.generate (Vector.length features) $ \featureIdx ->
           testState (features!featureIdx) (tests!testIdx)
  in sequence $ Vector.map sequence fv


-----------------
-- Computation --
-----------------

type CandidateFilter t = [ProgState t] -> [Assertion t] -> Assertion t -> Assertion t -> Ceili Bool

data PieEnv t = PieEnv { pe_names      :: Set Name
                       , pe_lits       :: Set t
                       , pe_goodTests  :: [ProgState t]
                       , pe_loopConds  :: [Assertion t]
                       , pe_goal       :: Assertion t
                       , pe_cfilters   :: [CandidateFilter t]
                       , pe_candidates :: Map Int (Set (Assertion t))
                       }

type PieM t a = StateT (PieEnv t) Ceili a

envGoodTests :: PieM t [ProgState t]
envGoodTests = do (PieEnv _ _ tests _ _ _ _) <- get; return tests

envLoopConds :: PieM t [Assertion t]
envLoopConds = do (PieEnv _ _ _ conds _ _ _) <- get; return conds

envGoal :: PieM t (Assertion t)
envGoal = do (PieEnv _ _ _ _ goal _ _) <- get; return goal

getFeatureCandidates :: ( Ord t
                        , Embeddable Integer t
                        , Pretty t
                        ) => Int -> PieM t (Set (Assertion t))
getFeatureCandidates size = do
  PieEnv names lits goodTests loopConds goal cfilters candidateMap <- get
  let mCandidates = Map.lookup size candidateMap
  case mCandidates of
    Just candidates -> return candidates
    Nothing -> do
      candidates <- lift $ do
        log_d $ "[PIE] Collecting and filtering feature candidates of size " ++ show size ++ "..."
        let lieqs = LI.linearInequalities names lits size
        let doFilter cfilter cLieqs = do
              lieqs' <- cLieqs
              filterM (cfilter goodTests loopConds goal) lieqs'
        filtered <- return . Set.fromList =<< foldr doFilter (return $ Set.toList lieqs) cfilters
        log_d $ "[PIE] Caching " ++ (show $ Set.size filtered) ++ " feature candidates with size "
            ++ show size ++ " (" ++ (show $ Set.size lieqs) ++ " before filtering)"
        log_d $ "***** Loop cond: " ++ (show loopConds)
        log_d $ "***** Allowed candidates: " ++ (show $ Set.toList filtered)
        log_d $ "***** Disallowed candidates: " ++ (show $ Set.toList $ lieqs Set.\\ filtered)
        return filtered
      let candidateMap' = Map.insert size candidates candidateMap
      put $ PieEnv names lits goodTests loopConds goal cfilters candidateMap'
      return candidates

getCandidatesUpToSize :: ( Ord t
                         , Embeddable Integer t
                         , Pretty t
                         ) => Int -> PieM t (Map Int (Set (Assertion t)))
getCandidatesUpToSize size = do
  candidates <- mapM getFeatureCandidates $ [0..size]
  return $ Map.fromList $ zip [0..size] candidates

plog_e :: String -> PieM t ()
plog_e msg = lift $ log_e msg

plog_i :: String -> PieM t ()
plog_i msg = lift $ log_i msg

plog_d :: String -> PieM t ()
plog_d msg = lift $ log_d msg


----------------
-- LoopInvGen --
----------------

loopInvGen :: ( Embeddable Integer t
              , Ord t
              , Pretty t
              , SMT.ValidCheckable t
              , StatePredicate (Assertion t) t
              , AssertionParseable t )
           => Set Name
           -> Set t
           -> [CandidateFilter t]
           -> BackwardPT c p t
           -> c
           -> [Assertion t]
           -> p
           -> Assertion t
           -> [ProgState t]
           -> Ceili (Maybe (Assertion t))
loopInvGen names literals candidateFilters backwardPT ctx conds body post goodTests = do
  log_i $ "[PIE] Beginning invariant inference with PIE"
  let task = loopInvGen' backwardPT ctx body
  evalStateT task $ PieEnv names literals goodTests conds post candidateFilters Map.empty

loopInvGen' :: ( Embeddable Integer t
               , Ord t
               , Pretty t
               , SMT.ValidCheckable t
               , StatePredicate (Assertion t) t
               , AssertionParseable t )
            => BackwardPT c p t
            -> c
            -> p
            -> PieM t (Maybe (Assertion t))
loopInvGen' backwardPT ctx body = do
  goodTests <- envGoodTests
  conds     <- envLoopConds
  goal      <- envGoal
  plog_i $ "[PIE] LoopInvGen searching for initial candidate invariant..."
  let nconds = And $ map Not conds
  mInvar <- vPreGen (Imp nconds goal)
                    (Vector.fromList goodTests)
                    Vector.empty
  lift . log_i $ "[PIE] LoopInvGen initial invariant: " ++ (show . pretty) mInvar
  case mInvar of
    Nothing -> do
      plog_i "[PIE] Unable to find initial candidate invariant (an I s.t. I /\\ ~c => Post)"
      return Nothing
    Just invar -> do
      mInvar' <- makeInductive backwardPT ctx body invar
      case mInvar' of
         Nothing -> do
           plog_i "[PIE] LoopInvGen unable to find inductive strengthening"
           return Nothing -- TODO: Not this.
         Just invar' -> do
           plog_i $ "[PIE] LoopInvGen strengthened (inductive) invariant: " ++ (show . pretty) mInvar'
           plog_i $ "[PIE] Attempting to weaken invariant..."
           let validInvar inv = lift $ do
                 wp <- backwardPT ctx body inv
                 checkValidB $ And [ Imp (And [nconds, inv]) goal
                                   , Imp (And $ inv:conds) wp ]
           weakenedInvar <- weaken validInvar invar'
           plog_i $ "[PIE] Inference complete. Learned invariant: " ++ (show . pretty) weakenedInvar
           return $ Just weakenedInvar

makeInductive :: ( Embeddable Integer t
                 , Ord t
                 , Pretty t
                 , SMT.ValidCheckable t
                 , StatePredicate (Assertion t) t
                 , AssertionParseable t )
              => BackwardPT c p t
              -> c
              -> p
              -> Assertion t
              -> PieM t (Maybe (Assertion t))
makeInductive backwardPT ctx body invar = do
  plog_d $ "[PIE] Checking inductivity of candidate invariant: " ++ (show . pretty) invar
  conds <- envLoopConds
  goodTests <- envGoodTests
  wp <- lift $ backwardPT ctx body invar
  let query = Imp (And $ invar:conds) wp
  response <- lift $ checkValid query
  mInvar <- case response of
    SMT.Valid        -> return $ Just invar
    SMT.Invalid _    -> return Nothing
    SMT.ValidUnknown -> do
      plog_e $ "[PIE] SMT solver returned unknown when checking inductivity. "
               ++ "Treating candidate as non-inductive. Inductivity SMT query: "
               ++ show query
      return Nothing
  case mInvar of
    Just _  -> do
      plog_i $ "[PIE] Candidate invariant is inductive"
      return mInvar
    Nothing -> do
      plog_i $ "[PIE] Candidate invariant not inductive, attempting to strengthen"
      inductiveWP <- lift $ backwardPT ctx body invar
      let goal = Imp (And $ invar:conds) inductiveWP
      mInvar' <- vPreGen goal (Vector.fromList goodTests) Vector.empty
      case mInvar' of
        Nothing -> do
          plog_d $ "[PIE] Unable to find inductive strengthening of " ++ show invar
          return Nothing
        Just invar' -> do
          plog_d $ "[PIE] Found strengthening candidate clause: " ++ show invar'
          makeInductive backwardPT ctx body (conj invar invar')

-- |A conjoin that avoids extraneous "and" nesting.
conj :: Assertion t -> Assertion t -> Assertion t
conj a1 a2 =
  case (a1, a2) of
    (And as, _) -> And (a2:as)
    (_, And as) -> And (a1:as)
    _           -> And [a1, a2]

weaken :: (Assertion t -> PieM t Bool) -> Assertion t -> PieM t (Assertion t)
weaken sufficient assertion = do
  let conj = conjuncts assertion
  conj' <- paretoOptimize (sufficient . conjoin) conj
  return $ conjoin conj'

conjuncts :: Assertion t -> [Assertion t]
conjuncts assertion = case assertion of
  And as -> concat $ map conjuncts as
  _      -> [assertion]

conjoin :: [Assertion t] -> Assertion t
conjoin as = case as of
  []     -> ATrue
  (a:[]) -> a
  _      -> And as

paretoOptimize :: ([Assertion t] -> PieM t Bool) -> [Assertion t] -> PieM t [Assertion t]
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


-------------
-- vPreGen --
-------------

vPreGen :: ( Embeddable Integer t
           , Ord t
           , Pretty t
           , SMT.ValidCheckable t
           , StatePredicate (Assertion t) t
           , AssertionParseable t )
        => (Assertion t)
        -> Vector (ProgState t)
        -> Vector (ProgState t)
        -> PieM t (Maybe (Assertion t))
vPreGen goal goodTests badTests = do
  plog_d $ "[PIE] Starting vPreGen pass"
  plog_d . show $ pretty "[PIE] goal: " <+> pretty goal
  plog_d . show $ pretty "[PIE] good tests: " <+> (align . prettyProgStates . Vector.toList) goodTests
  plog_d . show $ pretty "[PIE] bad tests: "  <+> (align . prettyProgStates . Vector.toList) badTests
  mCandidate <- pie Vector.empty goodTests badTests
  case mCandidate of
    Nothing -> return Nothing
    Just candidate -> do
      plog_d $ "[PIE] vPreGen candidate precondition: " ++ (show . pretty) candidate
      mCounter <- lift . findCounterexample $ Imp candidate goal
      case mCounter of
        Nothing -> do
          plog_d $ "[PIE] vPreGen found satisfactory precondition: " ++ show candidate
          return $ Just candidate
        Just counter -> do
          plog_d $ "[PIE] vPreGen found counterexample: " ++ show counter
          vPreGen goal goodTests $ Vector.cons (extractState counter) badTests

-- TODO: This is fragile.
extractState :: Pretty t => (Assertion t) -> (ProgState t)
extractState assertion = case assertion of
  Eq lhs rhs -> Map.fromList [(extractName lhs, extractInt rhs)]
  And as     -> Map.unions $ map extractState as
  _          -> error $ "Unexpected assertion: " ++ show assertion
  where
    extractName arith = case arith of
      Var name -> name
      _ -> error $ "Unexpected arith (expected name): " ++ show arith
    extractInt arith = case arith of
      Num n -> n
      _ -> error $ "Unexpected arith (expected int): " ++ show arith


---------
-- PIE --
---------

pie :: ( Embeddable Integer t
       , Ord t
       , Pretty t
       , StatePredicate (Assertion t) t )
    => Vector (Assertion t)
    -> Vector (ProgState t)
    -> Vector (ProgState t)
    -> PieM t (Maybe (Assertion t))
pie features goodTests badTests = do
  lift $ log_d $ "[PIE] Beginning PIE pass with features: " ++ show features
  posFV <- lift $ createFV features goodTests
  negFV <- lift $ createFV features badTests
  case getConflict posFV negFV goodTests badTests of
    Just (xGood, xBad) -> do
      mNewFeature <- findAugmentingFeature (Vector.take 8 xGood) (Vector.take 8 xBad)
      case mNewFeature of
        Nothing         -> return Nothing
        Just newFeature -> pie (Vector.cons newFeature features) goodTests badTests
    Nothing -> lift $ BL.learnBoolExpr features posFV negFV >>= return . Just

getConflict :: Vector FeatureVector
            -> Vector FeatureVector
            -> Vector (ProgState t)
            -> Vector (ProgState t)
            -> Maybe (Vector (ProgState t), Vector (ProgState t))
getConflict posFVs negFVs goodTests badTests = do
  conflict <- findConflict posFVs negFVs
  let posIndices = Vector.findIndices (== conflict) posFVs
  let negIndices = Vector.findIndices (== conflict) negFVs
  return (Vector.backpermute goodTests posIndices, Vector.backpermute badTests negIndices)

findConflict :: Vector FeatureVector -> Vector FeatureVector -> Maybe (Vector Bool)
findConflict posFVs negFVs = Vector.find (\pos -> isJust $ Vector.find (== pos) negFVs) posFVs

findAugmentingFeature :: ( Embeddable Integer t
                         , Ord t
                         , Pretty s
                         , Pretty t
                         , StatePredicate (Assertion t) s )
                      => Vector (ProgState s)
                      -> Vector (ProgState s)
                      -> PieM t (Maybe (Assertion t))
findAugmentingFeature xGood xBad = do
  let maxFeatureSize = 4 -- TODO: Don't hardcode max feature size
  let (goodTests, badTests) = (Vector.toList xGood, Vector.toList xBad)
  candidates <- getCandidatesUpToSize maxFeatureSize
  let getCandidates i = Map.findWithDefault Set.empty i candidates
  mNewFeature <- lift $ SL.findSeparator maxFeatureSize getCandidates goodTests badTests
  case mNewFeature of
    Just newFeature -> do
      return $ Just newFeature
    Nothing -> do
      case (Vector.length xGood < 2, Vector.length xBad < 2) of
        (True, True) -> plog_d "[PIE] Single conflict has no separating feature, giving up"
                        >> return Nothing
        (_, True)    -> plog_d "[PIE] Reducing conflict set in good tests"
                        >> findAugmentingFeature (halve xGood) xBad
        _            -> plog_d "[PIE] Reducing conflict set in bad tests"
                        >> findAugmentingFeature xGood (halve xBad)

halve :: Vector a -> Vector a
halve vec =
  let len = Vector.length vec
  in Vector.drop (max (len `quot` 2) 1) vec
