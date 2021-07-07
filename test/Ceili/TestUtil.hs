{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.TestUtil
  ( assertEquivalent
  , assertHasSameItems
  ) where

import Ceili.Assertion
import qualified Ceili.SMT as SMT
import qualified Data.Map as Map
import Data.Vector ( Vector )
import qualified Data.Vector as Vector
import System.Log.FastLogger
import Test.Framework

assertEquivalent :: Assertion -> Assertion -> IO ()
assertEquivalent a1 a2 = do
  let iff = And [ Imp a1 a2, Imp a2 a1 ]
  result <- withFastLogger LogNone $ \logger ->
            SMT.checkValidFL logger iff
  case result of
    SMT.Valid        -> return () -- pass
    SMT.Invalid s    -> assertFailure s
    SMT.ValidUnknown -> assertFailure "Unable to establish equivalence."

assertHasSameItems :: (Ord a, Show a) => Vector a -> Vector a -> IO ()
assertHasSameItems expectedVec actualVec = let
  addToCount item counts = let current = Map.findWithDefault 0 item counts
                           in Map.insert item (current + 1) counts
  countItems = Vector.foldr addToCount Map.empty
  in assertEqual (countItems expectedVec) (countItems actualVec)
