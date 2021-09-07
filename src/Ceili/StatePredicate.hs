{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Ceili.StatePredicate
  ( StatePredicate(..)
  , acceptsAll
  , rejectsAll
  ) where

import Ceili.Assertion
import Ceili.Evaluation
import Ceili.ProgState

class StatePredicate a s where
  testState :: a -> ProgState s -> Bool

instance StatePredicate (Assertion Integer) Integer where
  testState assertion state = eval () state assertion

acceptsAll :: (StatePredicate a s) => [ProgState s] -> a -> Bool
acceptsAll states assertion = and $ map (\state -> testState assertion state) states

rejectsAll :: (StatePredicate a s) => [ProgState s] -> a -> Bool
rejectsAll states assertion = and $ map (\state -> not $ testState assertion state) states
