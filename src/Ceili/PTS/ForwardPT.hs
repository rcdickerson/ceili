module Ceili.PTS.ForwardPT
  ( ForwardPT
  ) where

import Ceili.Assertion ( Assertion )

-- TODO: Replace IO with better monad.
type ForwardPT p = Assertion -> p -> IO Assertion
