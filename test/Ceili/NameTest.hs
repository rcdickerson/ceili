{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.NameTest(htf_thisModulesTests) where
import Test.Framework

import Ceili.Name
import Ceili.SMT
import qualified Data.Map as Map
import qualified Data.Set as Set

-- Dummy names for convenience.
x0 = Name "x" 0
x1 = Name "x" 1
x5 = Name "x" 5
y0 = Name "y" 0
y1 = Name "y" 1
z0 = Name "z" 0

test_buildNextFreshIds = let
  names = [ x0, x1, x5, y0, z0 ]
  expected = Map.fromList [ ("x", 6)
                          , ("y", 1)
                          , ("z", 1) ]
  actual = buildNextFreshIds names
  in assertEqual expected actual

test_buildNextFreshIdsEmpty = let
  names = [ ]
  expected = Map.empty
  actual = buildNextFreshIds names
  in assertEqual expected actual

test_freshen = let
  names = [ x0, x1, x5, y0, z0 ]
  nextIds = Map.fromList [ ("x", 10)
                         , ("y", 10)
                         , ("z", 10) ]
  expectedNames' = [ Name "x" 12
                   , Name "x" 11
                   , Name "x" 10
                   , Name "y" 10
                   , Name "z" 10 ]
  expectedNextIds' = Map.fromList [ ("x", 13)
                                  , ("y", 11)
                                  , ("z", 11) ]
  (actualNames', actualNextIds') = freshen names nextIds
  in do
    assertEqual expectedNames' actualNames'
    assertEqual expectedNextIds' actualNextIds'

test_fromString = do
  assertEqual (Name "x" 0) $ fromString "x"
  assertEqual (Name "x0" 0) $ fromString "x0"
  assertEqual (Name "x" 1) $ fromString "x!1"
  assertEqual (Name "x1" 0) $ fromString "x1!0"
  assertEqual (Name "x!1" 0) $ fromString "x!1!0"
  assertEqual (Name "x!1" 1) $ fromString "x!1!1"
  assertEqual (Name "x!" 0) $ fromString "x!"
  assertEqual (Name "x!1!2!3" 4) $ fromString "x!1!2!3!4"

test_name_toSMT = do
  assertEqual "x" (toSMT $ Name "x" 0)
  assertEqual "x!0" (toSMT $ Name "x!0" 0)
  assertEqual "x0" (toSMT $ Name "x0" 0)
  assertEqual "x!1" (toSMT $ Name "x" 1)
  assertEqual "x1" (toSMT $ Name "x1" 0)
  assertEqual "x!1!0" (toSMT $ Name "x!1!0" 0)
  assertEqual "x!1!1" (toSMT $ Name "x!1" 1)
  assertEqual "x!" (toSMT $ Name "x!" 0)
  assertEqual "x!!2" (toSMT $ Name "x!" 2)
  assertEqual "x!1!2!3!4" (toSMT $ Name "x!1!2!3" 4)

test_prefix = let
  names = [ x0, x1, x5, y0, z0 ]
  expected = [ Name "foo!x" 0
             , Name "foo!x" 1
             , Name "foo!x" 5
             , Name "foo!y" 0
             , Name "foo!z" 0 ]
  actual = prefix "foo!" names
  in assertEqual expected actual

test_substitute = let
  names = [ x0, x1, x5, y0, y1, z0 ]
  expected = [ x0 , Name "foo" 0, x5, y0, y1, z0 ]
  actual = substitute x1 (Name "foo" 0) names
  in assertEqual expected actual

test_substituteAll = let
  names = [ x0, x1, x5, y0, y1, z0 ]
  expected = [ x0, y0, y0, y0, y1, x1 ]
  actual = substituteAll [x1, x5, z0] [y0, y0, x1] names
  in assertEqual expected actual

test_substituteAll_swap = let
  names = [x0, x1]
  expected = [x1, x0]
  actual = substituteAll [x0, x1] [x1, x0] names
  in assertEqual expected actual

test_substituteHandle = let
  names = [ x0, x1, x5, y0, y1, z0 ]
  expected = [ Name "foo" 0
             , Name "foo" 1
             , Name "foo" 5
             , y0, y1, z0 ]
  actual = substituteHandle "x" "foo" names
  in assertEqual expected actual

test_subsituteAllHandles = let
  names = [ x0, x1, x5, y0, y1, z0 ]
  expected = [ Name "foo" 0
             , Name "foo" 1
             , Name "foo" 5
             , Name "bar" 0
             , Name "bar" 1
             , z0 ]
  actual = substituteAllHandles ["x", "y"] ["foo", "bar"] names
  in assertEqual expected actual

test_substituteAllHandles_swap = let
  names = [ Name "foo" 0, Name "bar" 1 ]
  expected = [ Name "bar" 0, Name "foo" 1 ]
  actual = substituteAllHandles ["foo", "bar"] ["bar", "foo"] names
  in assertEqual expected actual

test_mappableNames_name =
  assertEqual x1 $ mapNames (\_ -> x1) x0

test_collectableNames_name =
  assertEqual (Set.singleton x0) $ namesIn x0


-- Typed names

x0Int = TypedName x0 Int
x1Int = TypedName x1 Int
x0Bool = TypedName x0 Bool

test_mappableNames_typedName =
  assertEqual x1Int $ mapNames (\_ -> x1) x0Int

test_collectableNames_typedName =
  assertEqual (Set.singleton x0) $ namesIn x0Int

test_toSMT_typedName = do
  assertEqual "(x int)" $ toSMT x0Int
  assertEqual "(x!1 int)" $ toSMT x1Int
  assertEqual "(x bool)" $ toSMT x0Bool