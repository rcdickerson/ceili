{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Ceili.State
  ( State
  , pretty
  , withTypedKeys
  ) where

import Ceili.Name
import Data.Map ( Map )
import qualified Data.Map as Map
import Prettyprinter

type State = Map Name Integer

withTypedKeys :: State -> Map TypedName Integer
withTypedKeys = Map.mapKeys (\n -> TypedName n Int)

instance CollectableNames State where
  namesIn = Map.keysSet

instance MappableNames State where
  mapNames f = Map.mapKeys f

instance FreshableNames State where
  freshen state = do
    let assocs = Map.toList state
    assocs' <- mapM (\(k, v) -> do k' <- freshen k; return (k', v)) assocs
    return $ Map.fromList assocs'

instance Pretty State where
  pretty st = braces . hsep . (punctuate comma) $ map prettyAssoc assocList
    where
      assocList = Map.toList st
      prettyAssoc (k, v) = pretty k <+> "->" <+> pretty v
