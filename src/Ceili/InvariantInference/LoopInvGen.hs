{-# LANGUAGE FlexibleContexts #-}

-- An implementation of LoopInvGen (with the core PIE
-- component abstracted, see the Ceili.FeatureLearning.Pie module)
-- from "Data-driven precondition inference with learned features"
-- Padhi, Saswat, Rahul Sharma, and Todd Millstein
-- ACM SIGPLAN Notices 51.6 (2016): 42-56.
-- http://web.cs.ucla.edu/~todd/research/pldi16.pdf

module Ceili.InvariantInference.LoopInvGen
  ( loopInvGen
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Embedding
import Ceili.PTS ( BackwardPT )
import Ceili.ProgState
import qualified Ceili.SMT as SMT
import Ceili.StatePredicate
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State ( StateT, evalStateT, get )
import qualified Data.Map as Map
import Data.Vector ( Vector )
import qualified Data.Vector as Vector
import Prettyprinter


----------------
-- Separators --
----------------

type SeparatorLearner t = [ProgState t] -> [ProgState t] -> Ceili (Maybe (Assertion t))


-----------------
-- Computation --
-----------------

data LigEnv t = LigEnv { pe_goodTests        :: [ProgState t]
                       , pe_loopConds        :: [Assertion t]
                       , pe_goal             :: Assertion t
                       , pe_separatorLearner :: SeparatorLearner t
                       }

type LigM t a = StateT (LigEnv t) Ceili a

envGoodTests :: LigM t [ProgState t]
envGoodTests = return . pe_goodTests =<< get

envLoopConds :: LigM t [Assertion t]
envLoopConds = return . pe_loopConds =<< get

envGoal :: LigM t (Assertion t)
envGoal = return . pe_goal =<< get

envSeparatorLearner :: LigM t (SeparatorLearner t)
envSeparatorLearner = return . pe_separatorLearner =<< get

plog_e :: String -> LigM t ()
plog_e = lift . log_e

plog_i :: String -> LigM t ()
plog_i = lift . log_i

plog_d :: String -> LigM t ()
plog_d = lift . log_d


----------------
-- LoopInvGen --
----------------

loopInvGen :: ( Embeddable Integer t
              , Ord t
              , Pretty t
              , SMT.ValidCheckable t
              , StatePredicate (Assertion t) t
              , AssertionParseable t )
           => c
           -> BackwardPT c p t
           -> [Assertion t]
           -> p
           -> Assertion t
           -> [ProgState t]
           -> SeparatorLearner t
           -> Ceili (Maybe (Assertion t))
loopInvGen ctx backwardPT loopConds body post goodTests separatorLearner = do
  log_i $ "[LoopInvGen] Beginning invariant inference"
  let task = loopInvGen' ctx backwardPT body
  evalStateT task $ LigEnv goodTests loopConds post separatorLearner

loopInvGen' :: ( Embeddable Integer t
               , Ord t
               , Pretty t
               , SMT.ValidCheckable t
               , StatePredicate (Assertion t) t
               , AssertionParseable t )
            => c
            -> BackwardPT c p t
            -> p
            -> LigM t (Maybe (Assertion t))
loopInvGen' ctx backwardPT body = do
  goodTests <- envGoodTests
  conds     <- envLoopConds
  goal      <- envGoal
  plog_i $ "[LoopInvGen] Searching for initial candidate invariant..."
  let nconds = aAnd $ map Not conds
  mInvar <- vPreGen (aImp nconds goal)
                    Vector.empty
                    (Vector.fromList goodTests)
  case mInvar of
    Nothing -> do
      plog_i "[LoopInvGen] Unable to find initial candidate invariant (an I s.t. I /\\ ~c => Post)"
      return Nothing
    Just invar -> do
      lift . log_i $ "[LoopInvGen] Initial invariant: " ++ (show . pretty) mInvar
      mInvar' <- makeInductive backwardPT ctx body invar
      case mInvar' of
         Nothing -> do
           plog_i "[LoopInvGen] Unable to find inductive strengthening"
           return Nothing -- TODO: Not this.
         Just invar' -> do
           plog_i $ "[LoopInvGen] Strengthened (inductive) invariant: " ++ (show . pretty) mInvar'
           plog_i $ "[LoopInvGen] Attempting to weaken invariant..."
           let validInvar inv = lift $ do
                 wp <- backwardPT ctx body inv
                 checkValidB $ And [ Imp (And [nconds, inv]) goal
                                   , Imp (And $ inv:conds) wp ]
           weakenedInvar <- weaken validInvar invar'
           plog_i $ "[LoopInvGen] Inference complete. Learned invariant: " ++ (show . pretty) weakenedInvar
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
              -> LigM t (Maybe (Assertion t))
makeInductive backwardPT ctx body invar = do
  plog_d $ "[LoopInvGen] Checking inductivity of candidate invariant: " ++ (show . pretty) invar
  conds <- envLoopConds
  goodTests <- envGoodTests
  wp <- lift $ backwardPT ctx body invar
  let query = Imp (And $ invar:conds) wp
  response <- lift $ checkValid query
  mInvar <- case response of
    SMT.Valid        -> return $ Just invar
    SMT.Invalid _    -> return Nothing
    SMT.ValidUnknown -> do
      plog_e $ "[LoopInvGen] SMT solver returned unknown when checking inductivity. "
               ++ "Treating candidate as non-inductive. Inductivity SMT query: "
               ++ show query
      return Nothing
  case mInvar of
    Just _  -> do
      plog_i $ "[LoopInvGen] Candidate invariant is inductive"
      return mInvar
    Nothing -> do
      plog_i $ "[LoopInvGen] Candidate invariant not inductive, attempting to strengthen"
      inductiveWP <- lift $ backwardPT ctx body invar
      let goal = Imp (And $ invar:conds) inductiveWP
      mInvar' <- vPreGen goal Vector.empty (Vector.fromList goodTests)
      case mInvar' of
        Nothing -> do
          plog_d $ "[LoopInvGen] Unable to find inductive strengthening of " ++ show invar
          return Nothing
        Just invar' -> do
          plog_d $ "[LoopInvGen] Found strengthening candidate clause: " ++ show invar'
          makeInductive backwardPT ctx body (conj invar invar')

-- |A conjoin that avoids extraneous "and" nesting.
conj :: Assertion t -> Assertion t -> Assertion t
conj a1 a2 =
  case (a1, a2) of
    (And as, _) -> And (a2:as)
    (_, And as) -> And (a1:as)
    _           -> And [a1, a2]

weaken :: (Assertion t -> LigM t Bool) -> Assertion t -> LigM t (Assertion t)
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

paretoOptimize :: ([Assertion t] -> LigM t Bool) -> [Assertion t] -> LigM t [Assertion t]
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
        -> LigM t (Maybe (Assertion t))
vPreGen goal badTests goodTests = do
  plog_d $ "[LoopInvGen] Starting vPreGen pass"
  plog_d . show $ pretty "[LoopInvGen] goal: " <+> pretty goal
  plog_d . show $ pretty "[LoopInvGen] bad tests: "  <+> (align . prettyProgStates . Vector.toList) badTests
--  plog_d . show $ pretty "[LoopInvGen] good tests: " <+> (align . prettyProgStates . Vector.toList) goodTests
  sepLearner <- envSeparatorLearner
  mCandidate <- lift $ sepLearner (Vector.toList badTests) (Vector.toList goodTests)
  case mCandidate of
    Nothing -> return Nothing
    Just candidate -> do
      plog_d $ "[LoopInvGen] vPreGen candidate precondition: " ++ (show . pretty) candidate
      mCounter <- lift . findCounterexample $ Imp candidate goal
      case mCounter of
        Nothing -> do
          plog_d $ "[LoopInvGen] vPreGen found satisfactory precondition: " ++ show candidate
          return $ Just candidate
        Just counter -> do
          plog_d $ "[LoopInvGen] vPreGen found counterexample: " ++ show counter
          let badTests' = Vector.cons (extractState counter) badTests
          vPreGen goal badTests' goodTests

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
