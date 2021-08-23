module Ceili.FeatureLearning.Separator
  ( findSeparator
  ) where

import Ceili.Assertion
import Ceili.State
import Ceili.StatePredicate ( testState )
import Data.Set ( Set )
import qualified Data.Set as Set
import Ceili.CeiliEnv
import Data.Vector ( Vector )
import qualified Data.Vector as Vector

findSeparator :: Int
              -> (Int -> Set Assertion)
              -> Vector State
              -> Vector State
              -> Ceili (Maybe Assertion)
findSeparator maxCandidateSize candidatesOfSize goodTests badTests = let
  acceptsGoods assertion = and $ Vector.toList $
      Vector.map (\test -> testState assertion test) goodTests
  rejectsBads assertion = and $ Vector.toList $
      Vector.map (\test -> testState (Not assertion) test) badTests
  firstThatSeparates assertions =
    case assertions of
      []   -> Nothing
      a:as -> do
        if acceptsGoods a && rejectsBads a
          then Just a
          else firstThatSeparates as
  featureLearn' size = do
    log_d $ "[Separator] Examining candidate separators of size " ++ show size
    let mFeature = firstThatSeparates . Set.toList $ candidatesOfSize size
    case mFeature of
      Nothing ->
        if size >= maxCandidateSize
        then logMaxSizeReached maxCandidateSize >> return Nothing
        else featureLearn' (size + 1)
      Just feature -> do
        log_d $ "[Separator] Found separator: " ++ show feature
        return $ Just feature
  in do
    log_d   "[Separator] Beginning separator search"
    log_d $ "[Separator]   Good tests: " ++ (show $ Vector.map (show . pretty) goodTests)
    log_d $ "[Separator]   Bad tests: "  ++ (show $ Vector.map (show . pretty) badTests)
    featureLearn' 1

logMaxSizeReached :: Int -> Ceili ()
logMaxSizeReached maxSize = log_d $
  "[Separator] Could not find separator within size bound (" ++ show maxSize ++ ")"
