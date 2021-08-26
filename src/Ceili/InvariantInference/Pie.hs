-- An implementation of PIE / LoopInvGen invariant inference from
-- "Data-driven precondition inference with learned features"
-- Padhi, Saswat, Rahul Sharma, and Todd Millstein
-- ACM SIGPLAN Notices 51.6 (2016): 42-56.
-- http://web.cs.ucla.edu/~todd/research/pldi16.pdf

module Ceili.InvariantInference.Pie
  ( FeatureVector
  , PieEnv(..)
  , createFV
  , getConflict
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
import qualified Ceili.SMT as SMT
import Ceili.SMTString ( showSMT )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State ( StateT, evalStateT, get )
import Data.Maybe ( isJust )
import Data.Set ( Set )
import qualified Data.Map as Map
import Data.Vector ( Vector, (!) )
import qualified Data.Vector as Vector


---------------------
-- Feature Vectors --
---------------------
type FeatureVector = Vector Bool

createFV :: Vector Assertion -> Vector State -> Vector FeatureVector
createFV features tests = Vector.generate (Vector.length tests) $ \testIdx ->
                          Vector.generate (Vector.length features) $ \featureIdx ->
                          testState (features!featureIdx) (tests!testIdx)


-----------------
-- Computation --
-----------------

data PieEnv = PieEnv { pe_names :: Set TypedName
                     , pe_lits  :: Set Integer
                     }

type PieM a = StateT PieEnv Ceili a

plog_e :: String -> PieM ()
plog_e msg = lift $ log_e msg

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
  lits  <- getProgLits
  let task = loopInvGen' backwardPT ctx cond body post goodTests
  evalStateT task $ PieEnv names lits

loopInvGen' :: BackwardPT c p
            -> c
            -> Assertion
            -> p
            -> Assertion
            -> [State]
            -> PieM (Maybe Assertion)
loopInvGen' backwardPT ctx cond body post goodTests = do
  plog_i $ "[PIE] LoopInvGen searching for initial candidate invariant..."
  mInvar <- vPreGen (Imp (Not cond) post)
                    (Vector.fromList goodTests)
                    Vector.empty
  lift . log_i $ "[PIE] LoopInvGen initial invariant: " ++ (showSMT mInvar)
  case mInvar of
    Nothing -> do
      plog_i "[PIE] Unable to find initial candidate invariant (an I s.t. I /\\ ~c => Post)"
      return Nothing
    Just invar -> do
      mInvar' <- makeInductive backwardPT ctx cond body invar goodTests
      case mInvar' of
         Nothing -> do
           plog_i "[PIE] LoopInvGen unable to find inductive strengthening"
           return Nothing -- TODO: Not this.
         Just invar' -> do
           plog_i $ "[PIE] LoopInvGen strengthened (inductive) invariant: " ++ showSMT mInvar'
           plog_i $ "[PIE] Attempting to weaken invariant..."
           let validInvar inv = lift $ do
                 wp <- backwardPT ctx body inv
                 checkValidB $ And [ Imp (And [Not cond, inv]) post
                                  , Imp (And [cond, inv]) wp ]
           weakenedInvar <- weaken validInvar invar'
           plog_i $ "[PIE] Inference complete. Learned invariant: " ++ showSMT weakenedInvar
           return $ Just weakenedInvar

makeInductive :: BackwardPT c p
              -> c
              -> Assertion
              -> p
              -> Assertion
              -> [State]
              -> PieM (Maybe Assertion)
makeInductive backwardPT ctx cond body invar goodTests = do
  plog_d $ "[PIE] Checking inductivity of candidate invariant: " ++ showSMT invar
  wp <- lift $ backwardPT ctx body invar
  let query = Imp (And [invar, cond]) wp
  response <- lift $ checkValid query
  mInvar <- case response of
    SMT.Valid        -> return $ Just invar
    SMT.Invalid _    -> return Nothing
    SMT.ValidUnknown -> do
      plog_e $ "[PIE] SMT solver returned unknown when checking inductivity. "
               ++ "Treating candidate as non-inductive. Inductivity SMT query: "
               ++ showSMT query
      return Nothing
  case mInvar of
    Just _  -> do
      plog_i $ "[PIE] Candidate invariant is inductive"
      return mInvar
    Nothing -> do
      plog_i $ "[PIE] Candidate invariant not inductive, attempting to strengthen"
      inductiveWP <- lift $ backwardPT ctx body invar
      let goal = Imp (And [invar, cond]) inductiveWP
      mInvar' <- vPreGen goal (Vector.fromList goodTests) Vector.empty
      case mInvar' of
        Nothing -> do
          plog_d $ "[PIE] Unable to find inductive strengthening of " ++ showSMT invar
          return Nothing
        Just invar' -> do
          plog_d $ "[PIE] Found strengthening candidate clause: " ++ showSMT invar'
          makeInductive backwardPT ctx cond body (conj invar invar') goodTests

-- |A conjoin that avoids extraneous "and" nesting.
conj :: Assertion -> Assertion -> Assertion
conj a1 a2 =
  case (a1, a2) of
    (And as, _) -> And (a2:as)
    (_, And as) -> And (a1:as)
    _           -> And [a1, a2]

weaken :: (Assertion -> PieM Bool) -> Assertion -> PieM Assertion
weaken sufficient assertion = do
  let conj = conjuncts assertion
  conj' <- paretoOptimize (sufficient . conjoin) conj
  return $ conjoin conj'

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
        -> Vector State
        -> Vector State
        -> PieM (Maybe Assertion)
vPreGen goal goodTests badTests = do
  plog_d $ "[PIE] Starting vPreGen pass"
  plog_d $ "[PIE]   goal: "       ++ showSMT goal
  plog_d $ "[PIE]   good tests: " ++ (show $ Vector.map (show . pretty) goodTests)
  plog_d $ "[PIE]   bad tests: "  ++ (show $ Vector.map (show . pretty) badTests)
  mCandidate <- pie Vector.empty goodTests badTests
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
          vPreGen goal goodTests $ Vector.cons (extractState counter) badTests

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
    -> Vector State
    -> Vector State
    -> PieM (Maybe Assertion)
pie features goodTests badTests = do
  let posFV = createFV features goodTests
  let negFV = createFV features badTests
  case getConflict posFV negFV goodTests badTests of
    Just (xGood, xBad) -> do
      mNewFeature <- findAugmentingFeature (Vector.take 8 xGood) (Vector.take 8 xBad)
      case mNewFeature of
        Nothing         -> return Nothing
        Just newFeature -> pie (Vector.cons newFeature features) goodTests badTests
    Nothing -> lift $ BL.learnBoolExpr features posFV negFV >>= return . Just

getConflict :: Vector FeatureVector
            -> Vector FeatureVector
            -> Vector State
            -> Vector State
            -> Maybe (Vector State, Vector State)
getConflict posFVs negFVs goodTests badTests = do
  conflict <- findConflict posFVs negFVs
  let posIndices = Vector.findIndices (== conflict) posFVs
  let negIndices = Vector.findIndices (== conflict) negFVs
  return (Vector.backpermute goodTests posIndices, Vector.backpermute badTests negIndices)

findConflict :: Vector FeatureVector -> Vector FeatureVector -> Maybe (Vector Bool)
findConflict posFVs negFVs = Vector.find (\pos -> isJust $ Vector.find (== pos) negFVs) posFVs

findAugmentingFeature :: Vector State
                      -> Vector State
                      -> PieM (Maybe Assertion)
findAugmentingFeature xGood xBad = do
  let maxFeatureSize = 4 -- TODO: Don't hardcode max feature size
  PieEnv names lits <- get
  mNewFeature <- lift $ SL.findSeparator maxFeatureSize (LI.linearInequalities names lits) xGood xBad
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
