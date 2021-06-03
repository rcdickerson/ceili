{-# LANGUAGE TypeOperators #-}

module Ceili.PTS
  ( BackwardPT
  , ForwardPT
  ) where

import Ceili.Assertion ( Assertion )
import Ceili.CeiliEnv ( Ceili )

type BackwardPT c p = c -> p -> Assertion -> Ceili Assertion
type ForwardPT  c p = c -> p -> Assertion -> Ceili Assertion
