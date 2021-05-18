module Ceili.SMTString
  ( SMTString(..)
  , showSMT
  ) where

import Data.ByteString ( ByteString )
import Data.ByteString.Char8 ( pack, unpack )

class SMTString a where
  toSMT :: a -> ByteString

showSMT :: SMTString a => a -> String
showSMT = unpack . toSMT

instance SMTString a => SMTString (Maybe a) where
  toSMT Nothing  = pack "()"
  toSMT (Just x) = toSMT x
