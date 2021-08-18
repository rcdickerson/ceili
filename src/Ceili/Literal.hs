{-# LANGUAGE TypeOperators #-}

module Ceili.Literal
  ( CollectableLiterals(..)
  ) where

import Ceili.Language.Compose
import Data.Set ( Set )
import qualified Data.Set as Set

class CollectableLiterals e where
  litsIn :: e -> Set Integer

instance (CollectableLiterals (f e), CollectableLiterals (g e)) =>
         CollectableLiterals ((f :+: g) e) where
  litsIn (Inl f) = litsIn f
  litsIn (Inr f) = litsIn f

instance CollectableLiterals a => CollectableLiterals [a] where
  litsIn as = Set.unions $ map litsIn as
