module Ceili.InvariantInference.Houdini
  ( infer
  ) where

import Ceili.Assertion ( Assertion(..) )
import Ceili.InvariantInference.LinearInequalities
import Ceili.Name ( TypedName )
import qualified Ceili.SMT as SMT
import Ceili.SMTString ( showSMT )
import Control.Concurrent.Timeout ( timeout )
import Control.Monad ( filterM )
import Control.Monad.IO.Class ( liftIO )
import Data.Set ( Set )
import qualified Data.Set as Set
import System.IO ( hFlush, stdout )

infer :: Set TypedName
      -> Set Integer
      -> Int
      -> Assertion
      -> (Assertion -> IO Assertion)
      -> IO Assertion
infer names lits size precond computeSP = do
  hLog "Beginning invariant inference with Houdini"
  hLog $ (show $ Set.size names) ++ " names, "
      ++ (show $ Set.size lits) ++ " lits"
  candidates <- findCandidates names lits size precond
  hLog $ "Filtered candidates: " ++ (show $ length candidates)
  inductiveClauses <- houdini candidates computeSP
  hLog $ "Invariant: " ++ (showSMT $ And inductiveClauses)
  return $ And inductiveClauses

findCandidates :: Set TypedName
               -> Set Integer
               -> Int
               -> Assertion
               -> IO [Assertion]
findCandidates names lits size precond = do
  let candidates = linearInequalities names lits size
  hLog $ "Initial candidates: " ++ (show $ Set.size candidates)
  filterM (checkValid . Imp precond) $ Set.toList candidates

houdini :: [Assertion]
        -> (Assertion -> IO Assertion)
        -> IO [Assertion]
houdini candidates computeSP = do
  hLog $ "Starting houdini pass with "
    ++ (show $ length candidates)
    ++ " candidate clauses."
  sp <- computeSP $ And $ candidates
  inductive <- filterM (checkValid . Imp sp) candidates
  if (length inductive == length candidates)
    then return candidates
    else houdini inductive computeSP

-- TODO: These belong in some kind of config environment.
withTimeout t = liftIO $ timeout (1000000 * 2) t
hLog msg = do
  putStrLn msg
  hFlush stdout

checkValid :: Assertion -> IO Bool
checkValid assertion = do
  result <- withTimeout $ SMT.checkValid assertion
  case result of
    Nothing               -> do hLog "SMT timeout"; return False
    Just SMT.Valid        -> return True
    Just (SMT.Invalid _)  -> return False
    Just SMT.ValidUnknown -> do hLog "SMT unknown"; return False
