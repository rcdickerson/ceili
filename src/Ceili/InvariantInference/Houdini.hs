-- Loop invariance inspired by Houdini.
-- "Houdini, an annotation assistant for ESC/Java."
-- Flanagan, Cormac, and K. Rustan M. Leino
-- International Symposium of Formal Methods Europe.
-- Springer, Berlin, Heidelberg, 2001.

module Ceili.InvariantInference.Houdini
  ( infer
  ) where

import Ceili.Assertion ( Assertion(..) )
import Ceili.CeiliEnv
import Ceili.FeatureLearning.LinearInequalities
import Ceili.Name ( TypedName )
import qualified Ceili.SMT as SMT
import Ceili.SMTString ( showSMT )
import Control.Monad ( filterM )
import Data.Set ( Set )
import qualified Data.Set as Set

infer :: Set TypedName
      -> Set Integer
      -> Int
      -> Assertion
      -> (Assertion -> Ceili Assertion)
      -> Ceili Assertion
infer names lits size precond computeSP = do
  log_i "[Houdini] Beginning invariant inference with Houdini"
  log_d $ (show $ Set.size names) ++ " names, "
       ++ (show $ Set.size lits) ++ " lits"
  candidates <- findCandidates names lits size precond
  log_d $ "[Houdini] Filtered candidates: " ++ (show $ length candidates)
  inductiveClauses <- houdini candidates computeSP
  log_i $ "[Houdini] Invariant: " ++ (showSMT $ And inductiveClauses)
  return $ And inductiveClauses

findCandidates :: Set TypedName
               -> Set Integer
               -> Int
               -> Assertion
               -> Ceili [Assertion]
findCandidates names lits size precond = do
  let candidates = linearInequalities names lits size
  log_d $ "[Houdini] Initial candidate size: " ++ (show $ Set.size candidates)
  filterM (checkValidB . Imp precond) $ Set.toList candidates

houdini :: [Assertion]
        -> (Assertion -> Ceili Assertion)
        -> Ceili [Assertion]
houdini candidates computeSP = do
  log_i $ "[Houdini] Starting pass with "
    ++ (show $ length candidates)
    ++ " candidate clauses."
  sp <- computeSP $ And candidates
  let isValid candidate = do
        valid <- checkValidWithLog LogLevelNone $ Imp sp candidate
        return $ case valid of
          SMT.Valid -> True
          _         -> False
  inductive <- filterM isValid candidates
  if (length inductive == length candidates)
    then return candidates
    else houdini inductive computeSP
