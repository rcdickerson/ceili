{-# LANGUAGE TypeOperators #-}

module Ceili.PTS.ForwardPT
  ( ForwardPT(..)
  ) where

import Ceili.Assertion ( Assertion )
import Ceili.CeiliEnv ( Ceili )
import Ceili.Language.Compose

class ForwardPT p where
  forwardPT :: Assertion -> p -> Ceili Assertion

instance (ForwardPT (f e), ForwardPT (g e)) => ForwardPT ((f :+: g) e) where
  forwardPT pre (Inl f) = forwardPT pre f
  forwardPT pre (Inr g) = forwardPT pre g
