{-# LANGUAGE TypeOperators #-}

module Ceili.PTS
  ( BackwardPT(..)
  , ForwardPT(..)
  ) where

import Ceili.Assertion ( Assertion )
import Ceili.CeiliEnv ( Ceili )
import Ceili.Language.Compose

class BackwardPT p where
  backwardPT :: Assertion -> p -> Ceili Assertion

instance (BackwardPT (f e), BackwardPT (g e)) => BackwardPT ((f :+: g) e) where
  backwardPT post (Inl f) = backwardPT post f
  backwardPT post (Inr g) = backwardPT post g


class ForwardPT p where
  forwardPT :: Assertion -> p -> Ceili Assertion

instance (ForwardPT (f e), ForwardPT (g e)) => ForwardPT ((f :+: g) e) where
  forwardPT pre (Inl f) = forwardPT pre f
  forwardPT pre (Inr g) = forwardPT pre g
