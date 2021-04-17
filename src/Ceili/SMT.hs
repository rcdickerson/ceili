module Ceili.SMT
  ( ToSMT(..)
  ) where

class ToSMT a where
  toSMT :: a -> String
