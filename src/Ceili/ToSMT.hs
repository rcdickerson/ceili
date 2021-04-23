module Ceili.ToSMT
  ( ToSMT(..)
  ) where

class ToSMT a where
  toSMT :: a -> String
