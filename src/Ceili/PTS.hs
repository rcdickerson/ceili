{-# LANGUAGE TypeOperators #-}

module Ceili.PTS
  ( BackwardPT
  , ForwardPT
  ) where

import Ceili.Assertion ( Assertion )
import Ceili.CeiliEnv ( Ceili )

type BackwardPT p = p -> Assertion -> Ceili Assertion
type ForwardPT  p = p -> Assertion -> Ceili Assertion
