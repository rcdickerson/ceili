module Ceili.PTS.ForwardPT
  ( ForwardPT
  ) where

import Ceili.Assertion ( Assertion )

type ForwardPT a = Assertion -> a -> Assertion
