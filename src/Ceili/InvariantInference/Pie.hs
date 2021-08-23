-- An implementation of PIE / LoopInvGen invariant inference from
-- "Data-driven precondition inference with learned features"
-- Padhi, Saswat, Rahul Sharma, and Todd Millstein
-- ACM SIGPLAN Notices 51.6 (2016): 42-56.
-- http://web.cs.ucla.edu/~todd/research/pldi16.pdf

module Ceili.InvariantInference.Pie
  ( PieEnv(..)
  , pie
  , loopInvGen
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import qualified Ceili.FeatureLearning.LinearInequalities as LI
import qualified Ceili.FeatureLearning.PACBoolean as BL
import qualified Ceili.FeatureLearning.Separator as SL
import Ceili.Name
import Ceili.PTS ( BackwardPT )
import Ceili.State
import Ceili.StatePredicate
import Ceili.SMTString ( showSMT )
import Control.Monad ( filterM )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State ( StateT, evalStateT, get )
import Data.Maybe ( isJust )
import Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Vector ( Vector, (!) )
import qualified Data.Vector as Vector


---------------------
-- Feature Vectors --
---------------------
type FeatureVector = Vector (Vector Bool)

createFV :: Vector Assertion -> Vector State -> FeatureVector
createFV features tests = Vector.generate (Vector.length tests) $ \testIdx ->
                          Vector.generate (Vector.length features) $ \featureIdx ->
                          testState (features!featureIdx) (tests!testIdx)


-----------------
-- Computation --
-----------------

data PieEnv = PieEnv { pe_names       :: Set TypedName
                     , pe_lits        :: Set Integer
                     }

type PieM a = StateT PieEnv Ceili a

plog_i :: String -> PieM ()
plog_i msg = lift $ log_i msg

plog_d :: String -> PieM ()
plog_d msg = lift $ log_d msg


----------------
-- LoopInvGen --
----------------

loopInvGen :: (CollectableNames p) =>
              BackwardPT c p
           -> c
           -> Assertion
           -> p
           -> Assertion
           -> [State]
           -> Ceili (Maybe Assertion)
loopInvGen backwardPT ctx cond body post goodTests = do
  log_i $ "[PIE] Beginning invariant inference with PIE"
  names <- getProgNames
  lits <- getProgLits
  let task = loopInvGen' backwardPT ctx cond body post Set.empty goodTests
  evalStateT task $ PieEnv names lits

loopInvGen' :: BackwardPT c p
            -> c
            -> Assertion
            -> p
            -> Assertion
            -> Set Assertion
            -> [State]
            -> PieM (Maybe Assertion)
loopInvGen' backwardPT ctx cond body post denylist goodTests = do
  plog_i $ "[PIE] LoopInvGen searching for initial candidate invariant..."
  mInvar <- vPreGen (Imp (Not cond) post)
                    denylist
                    (Vector.fromList goodTests)
                    Vector.empty
  lift . log_i $ "[PIE] LoopInvGen initial invariant: " ++ (showSMT mInvar)
  case mInvar of
    Nothing -> plog_i "[PIE] Unable to find initial candidate invariant"
               >> return Nothing
    Just invar -> do
      mInvar' <- makeInductive backwardPT ctx cond body invar denylist goodTests
      case mInvar' of
         Nothing -> do
           plog_i "[PIE] LoopInvGen unable to find inductive strengthening, backtracking"
           -- On every pass, filter out the non-inductive candidate clauses.
           let nonInductive a = do
                 wp <- backwardPT ctx body a
                 (return . not) =<< (checkValidB $ Imp (And [cond, a]) wp)
           nonInductiveConjs <- conjunctsMeeting nonInductive invar
           let denylist' = Set.union denylist $ Set.fromList $ concat $ map cnfAtoms nonInductiveConjs
           loopInvGen' backwardPT ctx cond body post denylist' goodTests
         Just invar' -> do
           plog_i $ "[PIE] LoopInvGen strengthened (inductive) invariant: " ++ (showSMT mInvar')
           plog_i $ "[PIE] Attempting to weaken invariant..."
           let validInvar inv = lift $ do
                 wp <- backwardPT ctx body inv
                 checkValidB $ And [ Imp (And [Not cond, inv]) post
                                  , Imp (And [cond, inv]) wp ]
           weakenedInvar <- weaken validInvar invar'
           plog_i $ "[PIE] Learned invariant: " ++ showSMT weakenedInvar
           return $ Just weakenedInvar
      -- The PIE paper now looks for a contradiction with the precond and then weakens
      -- the invariant if needed. We don't have a precond in the case where we are
      -- looking for a WP in our PTS, so leave this off for now. (Instead, we do a Pareto
      -- optimality weakening by iteratively removing clauses unneeded to establish the
      -- invariant / post -- see `weaken` below.)
      --
      -- The code for precondition-based weakening would be something like:
      --
      -- mCounter <- findCounterexample $ Imp precond invar'
      -- case mCounter of
      --    Nothing -> return $ Just invar'
      --    Just counter -> do
      --      log_d $ "[PIE] LoopInvGen found counterexample to strengthened invariant: "
      --            ++ (showSMT counter)
      --      loopInvGen cond body post (counter:goodTests)

makeInductive :: BackwardPT c p
              -> c
              -> Assertion
              -> p
              -> Assertion
              -> Set Assertion
              -> [State]
              -> PieM (Maybe Assertion)
makeInductive backwardPT ctx cond body invar denylist goodTests = do
  wp <- lift $ backwardPT ctx body invar
  inductive <- lift $ checkValidB $ Imp (And [invar, cond]) wp
  case inductive of
    True -> return $ Just invar
    False -> do
      plog_i $ "[PIE] LoopInvGen invariant not inductive, attempting to strengthen..."
      inductiveWP <- lift $ backwardPT ctx body invar
      mInvar' <- vPreGen (Imp (And [invar, cond]) inductiveWP)
                         denylist
                         (Vector.fromList goodTests)
                         Vector.empty
      case mInvar' of
        Nothing -> return Nothing
        Just invar' -> makeInductive backwardPT
                                     ctx
                                     cond
                                     body
                                     (And [invar, invar'])
                                     denylist
                                     goodTests

conjunctsMeeting :: (Assertion -> Ceili Bool) -> Assertion -> PieM [Assertion]
conjunctsMeeting check assertion = lift $ filterM check $ conjuncts assertion

weaken :: (Assertion -> PieM Bool) -> Assertion -> PieM Assertion
weaken sufficient assertion = do
  let conj = conjuncts assertion
  conj' <- paretoOptimize (sufficient . conjoin) conj
  return $ conjoin conj'

cnfAtoms :: Assertion -> [Assertion]
cnfAtoms assertion = case assertion of
  And as -> concat $ map cnfAtoms as
  Or as  -> concat $ map cnfAtoms as
  _      -> [assertion]


conjuncts :: Assertion -> [Assertion]
conjuncts assertion = case assertion of
  And as -> concat $ map conjuncts as
  _      -> [assertion]

conjoin :: [Assertion] -> Assertion
conjoin as = case as of
  []     -> ATrue
  (a:[]) -> a
  _      -> And as

paretoOptimize :: ([Assertion] -> PieM Bool) -> [Assertion] -> PieM [Assertion]
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

vPreGen :: Assertion
        -> Set Assertion
        -> Vector State
        -> Vector State
        -> PieM (Maybe Assertion)
vPreGen goal denylist goodTests badTests = do
  plog_d $ "[PIE] Starting vPreGen pass"
  plog_d $ "[PIE]   goal: "       ++ showSMT goal
  plog_d $ "[PIE]   good tests: " ++ (show $ Vector.map (show . pretty) goodTests)
  plog_d $ "[PIE]   bad tests: "  ++ (show $ Vector.map (show . pretty) badTests)
  mCandidate <- pie Vector.empty denylist goodTests badTests
  case mCandidate of
    Nothing -> return Nothing
    Just candidate -> do
      plog_d $ "[PIE] vPreGen candidate precondition: " ++ showSMT candidate
      mCounter <- lift $ findCounterexample $ Imp candidate goal
      case mCounter of
        Nothing -> do
          plog_d $ "[PIE] vPreGen found satisfactory precondition: " ++ showSMT candidate
          return $ Just candidate
        Just counter -> do
          plog_d $ "[PIE] vPreGen found counterexample: " ++ showSMT counter
          vPreGen goal denylist goodTests $ Vector.cons (extractState counter) badTests

-- TODO: This is fragile.
extractState :: Assertion -> State
extractState assertion = case assertion of
  Eq lhs rhs -> Map.fromList [(extractName lhs, extractInt rhs)]
  And as     -> Map.unions $ map extractState as
  _          -> error $ "Unexpected assertion: " ++ show assertion
  where
    extractName arith = case arith of
      Var (TypedName name _) -> name
      _ -> error $ "Unexpected arith (expected name): " ++ show arith
    extractInt arith = case arith of
      Num n -> n
      _ -> error $ "Unexpected arith (expected int): " ++ show arith

---------
-- PIE --
---------

pie :: Vector Assertion
    -> Set Assertion
    -> Vector State
    -> Vector State
    -> PieM (Maybe Assertion)
pie features denylist goodTests badTests = do
  let posFV = createFV features goodTests
  let negFV = createFV features badTests
  case getConflict posFV negFV goodTests badTests of
    Just (xGood, xBad) -> do
      mNewFeature <- findAugmentingFeature denylist xGood xBad
      case mNewFeature of
        Nothing         -> return Nothing
        Just newFeature -> pie (Vector.cons newFeature features) denylist goodTests badTests
    Nothing -> lift $ BL.learnBoolExpr features posFV negFV >>= return . Just

getConflict :: FeatureVector
            -> FeatureVector
            -> Vector State
            -> Vector State
            -> Maybe (Vector State, Vector State)
getConflict posFV negFV goodTests badTests = do
  conflict <- findConflict posFV negFV
  let posIndices = Vector.findIndices (== conflict) posFV
  let negIndices = Vector.findIndices (== conflict) negFV
  return (Vector.backpermute goodTests posIndices, Vector.backpermute badTests negIndices)

findConflict :: FeatureVector -> FeatureVector -> Maybe (Vector Bool)
findConflict posFV negFV = Vector.find (\pos -> isJust $ Vector.find (== pos) negFV) posFV

findAugmentingFeature :: Set Assertion
                      -> Vector State
                      -> Vector State
                      -> PieM (Maybe Assertion)
findAugmentingFeature denylist xGood xBad = do
  let maxFeatureSize = 4 -- TODO: Don't hardcode max feature size
  PieEnv names lits <- get
  mNewFeature <- lift $ SL.findSeparator maxFeatureSize (LI.linearInequalities names lits) xGood xBad
  case mNewFeature of
    Just newFeature -> do
      return $ Just newFeature
    Nothing -> do
      case (Vector.length xGood, Vector.length xBad) of
        (1, 1) -> plog_d "[PIE] Single conflict has no separating feature, giving up"
                  >> return Nothing
        (_, 1) -> plog_d "[PIE] Reducing conflict set in good tests" >>
                  findAugmentingFeature denylist (halve xGood) xBad
        _      -> plog_d "[PIE] Reducing conflict set in bad tests" >>
                  findAugmentingFeature denylist xGood (halve xBad)

halve :: Vector a -> Vector a
halve vec =
  let len = Vector.length vec
  in Vector.drop (max (len `quot` 2) 1) vec
