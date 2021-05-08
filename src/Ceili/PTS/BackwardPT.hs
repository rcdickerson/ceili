{-# LANGUAGE TypeOperators #-}

module Ceili.PTS.BackwardPT
  ( BackwardPT(..)
  ) where

import Ceili.Assertion ( Assertion )
import Ceili.CeiliEnv ( Ceili )
import Ceili.Language.Compose

class BackwardPT p where
  backwardPT :: Assertion -> p -> Ceili Assertion

instance (BackwardPT (f e), BackwardPT (g e)) => BackwardPT ((f :+: g) e) where
  backwardPT post (Inl f) = backwardPT post f
  backwardPT post (Inr g) = backwardPT post g
