module Ceili.PTS.ForwardPT
  ( ForwardPT(..)
  ) where

import Ceili.Assertion ( Assertion )
import Ceili.CeiliEnv ( Ceili )

class ForwardPT p where
  forwardPT :: Assertion -> p -> Ceili Assertion
