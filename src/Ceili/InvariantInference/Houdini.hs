module Ceili.InvariantInference.Houdini
  (
  ) where

import Ceili.Assertion ( Assertion(..) )
import Ceili.InvariantInference.LinearInequalities
import Ceili.Name ( TypedName )
import Ceili.PTS.ForwardPT
import qualified Ceili.SMT as SMT
import Control.Concurrent.Timeout ( timeout )
import Control.Monad ( filterM )
import Control.Monad.IO.Class ( liftIO )
import Data.Set ( Set )
import qualified Data.Set as Set

infer :: ForwardPT p -> Assertion -> Assertion
infer forwardPT precond = ATrue

findCandidates :: Set TypedName
               -> Set Integer
               -> Int
               -> Assertion
               -> IO (Set Assertion)
findCandidates names lits depth precond = do
  let candidates = linearInequalities names lits depth
  filtered <- filterM (checkValid . Imp precond) $ Set.toList candidates
  return $ Set.fromList filtered

-- TODO: These belong in some kind of SMT monad.
withTimeout t = liftIO $ timeout (1000000 * 2) t
smtLog = putStrLn

checkValid :: Assertion -> IO Bool
checkValid assertion = do
  result <- withTimeout $ SMT.checkValid assertion
  case result of
    Nothing               -> do smtLog "SMT timeout"; return False
    Just SMT.Valid        -> return True
    Just (SMT.Invalid _)  -> return False
    Just SMT.ValidUnknown -> do smtLog "SMT unknown"; return False
