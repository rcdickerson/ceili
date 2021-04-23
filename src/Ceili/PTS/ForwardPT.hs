module Ceili.PTS.ForwardPT
  ( ForwardPT
  ) where

import Ceili.Assertion ( Assertion )

type ForwardPT p = Assertion -> p -> Assertion
