module Ceili.InvariantInference.Houdini
  ( infer
  ) where

import Ceili.Assertion ( Assertion(..) )
import Ceili.CeiliEnv
import Ceili.InvariantInference.LinearInequalities
import Ceili.Name ( TypedName )
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
  log_i "Beginning invariant inference with Houdini"
  log_d $ (show $ Set.size names) ++ " names, "
       ++ (show $ Set.size lits) ++ " lits"
  candidates <- findCandidates names lits size precond
  log_d $ "Filtered candidates: " ++ (show $ length candidates)
  inductiveClauses <- houdini candidates computeSP
  log_i $ "Invariant: " ++ (showSMT $ And inductiveClauses)
  return $ And inductiveClauses

findCandidates :: Set TypedName
               -> Set Integer
               -> Int
               -> Assertion
               -> Ceili [Assertion]
findCandidates names lits size precond = do
  let candidates = linearInequalities names lits size
  log_d $ "Initial candidate size: " ++ (show $ Set.size candidates)
  filterM (checkValid . Imp precond) $ Set.toList candidates

houdini :: [Assertion]
        -> (Assertion -> Ceili Assertion)
        -> Ceili [Assertion]
houdini candidates computeSP = do
  log_i $ "Starting houdini pass with "
    ++ (show $ length candidates)
    ++ " candidate clauses."
  sp <- computeSP $ And candidates
  inductive <- filterM (checkValidWithLog LogLevelNone . Imp sp) candidates
  if (length inductive == length candidates)
    then return candidates
    else houdini inductive computeSP
