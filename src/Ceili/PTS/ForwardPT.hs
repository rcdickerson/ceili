module Ceili.PTS.ForwardPT
  ( ForwardPT
  ) where

import Ceili.Assertion ( Assertion )
import Ceili.CeiliEnv ( Ceili )

-- TODO: Replace IO with better monad.
type ForwardPT p = Assertion -> p -> Ceili Assertion
