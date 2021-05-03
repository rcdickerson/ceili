module Ceili.PTS.BackwardPT
  ( BackwardPT(..)
  ) where

import Ceili.Assertion ( Assertion )
import Ceili.CeiliEnv ( Ceili )

class BackwardPT p where
  backwardPT :: Assertion -> p -> Ceili Assertion
