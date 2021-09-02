{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Ceili.StatePredicate
  ( StatePredicate(..)
  , acceptsAll
  , rejectsAll
  ) where

import Ceili.ProgState

class StatePredicate a s where
  testState :: a -> ProgState s -> Bool

acceptsAll :: (StatePredicate a s) => [ProgState s] -> a -> Bool
acceptsAll states assertion = and $ map (\state -> testState assertion state) states

rejectsAll :: (StatePredicate a s) => [ProgState s] -> a -> Bool
rejectsAll states assertion = and $ map (\state -> not $ testState assertion state) states
