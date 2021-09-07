{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Ceili.ProgState
  ( ProgState
  , pretty
  , prettySMTState
  , withIntTypedKeys
  ) where

import Ceili.Name
import Ceili.SMTString
import Data.Map ( Map )
import qualified Data.Map as Map
import Prettyprinter

type ProgState a = Map Name a

withIntTypedKeys :: Integral a => (ProgState a) -> Map TypedName a
withIntTypedKeys = Map.mapKeys (\n -> TypedName n Int)

instance CollectableNames (ProgState a) where
  namesIn = Map.keysSet

instance MappableNames (ProgState a) where
  mapNames f = Map.mapKeys f

instance FreshableNames (ProgState a) where
  freshen state = do
    let assocs = Map.toList state
    assocs' <- mapM (\(k, v) -> do k' <- freshen k; return (k', v)) assocs
    return $ Map.fromList assocs'

instance Pretty a => Pretty (ProgState a) where
  pretty st = braces . hsep . (punctuate comma) $ map prettyAssoc assocList
    where
      assocList = Map.toList st
      prettyAssoc (k, v) = pretty k <+> "->" <+> pretty v

prettySMTState :: SMTString a => ProgState a -> String
prettySMTState state = show . pretty $ Map.map showSMT state
