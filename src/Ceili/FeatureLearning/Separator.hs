{-# LANGUAGE FlexibleContexts #-}

module Ceili.FeatureLearning.Separator
  ( findSeparator
  ) where

import Ceili.CeiliEnv
import Ceili.SMTString
import Ceili.ProgState
import Ceili.StatePredicate
import Data.Set ( Set )
import qualified Data.Set as Set

findSeparator :: (SMTString p, SMTString s, StatePredicate p s) =>
                 Int
              -> (Int -> Set p)
              -> [ProgState s]
              -> [ProgState s]
              -> Ceili (Maybe p)
findSeparator maxCandidateSize candidatesOfSize goodTests badTests = let
  featureLearn' size = do
    log_d $ "[Separator] Examining candidate separators of size " ++ show size
    let candidates = Set.toList $ candidatesOfSize size
    let mFeature = firstThatSeparates goodTests badTests candidates
    case mFeature of
      Nothing ->
        if size >= maxCandidateSize
        then logMaxSizeReached maxCandidateSize >> return Nothing
        else featureLearn' (size + 1)
      Just feature -> do
        log_d $ "[Separator] Found separator: " ++ showSMT feature
        return $ Just feature
  in do
    log_d   "[Separator] Beginning separator search"
    log_d $ "[Separator]   Good tests: " ++ (show $ map prettySMTState goodTests)
    log_d $ "[Separator]   Bad tests: "  ++ (show $ map prettySMTState badTests)
    featureLearn' 1

firstThatSeparates :: StatePredicate p s
                   => [ProgState s]
                   -> [ProgState s]
                   -> [p]
                   -> Maybe p
firstThatSeparates goodTests badTests assertions =
  case assertions of
    []   -> Nothing
    a:as -> do
      if acceptsAll goodTests a && rejectsAll badTests a
        then Just a
        else firstThatSeparates goodTests badTests as

logMaxSizeReached :: Int -> Ceili ()
logMaxSizeReached maxSize = log_d $
  "[Separator] Could not find separator within size bound (" ++ show maxSize ++ ")"
