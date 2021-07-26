module Ceili.State
  ( State
  , withTypedKeys
  ) where

import Ceili.Name
import Data.Map ( Map )
import qualified Data.Map as Map

type State = Map Name Integer

withTypedKeys :: State -> Map TypedName Integer
withTypedKeys = Map.mapKeys (\n -> TypedName n Int)
