{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Ceili.StatePredicate
  ( StatePredicate(..)
  , acceptsAll
  , rejectsAll
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Evaluation
import Ceili.ProgState

class StatePredicate a s where
  testState :: a -> ProgState s -> Ceili Bool

instance StatePredicate (Assertion Integer) Integer where
  testState assertion state = return $ eval () state assertion

acceptsAll :: (StatePredicate a s) => [ProgState s] -> a -> Ceili Bool
acceptsAll states assertion = return . and =<< mapM (\state -> testState assertion state) states

rejectsAll :: (StatePredicate a s) => [ProgState s] -> a -> Ceili Bool
rejectsAll states assertion = return . and =<< mapM (\state -> return . not =<< testState assertion state) states
