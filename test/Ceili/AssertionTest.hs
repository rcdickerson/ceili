{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.AssertionTest(htf_thisModulesTests) where
import Test.Framework

import qualified Data.Set as Set
import Ceili.Assertion
import Ceili.AssertionGen()
import Ceili.Name

-- Some dummy names and assertions for convenience.
x0 = TypedName (Name "x" 0) Int
x1 = TypedName (Name "x" 1) Int
x2 = TypedName (Name "x" 2) Int
y0 = TypedName (Name "y" 0) Int


assertion1 = Not $ And [ Eq (Var x0) (Add [Num 5, Var y0])
                       , Lt (Var x1) (Var x2)
                       ]
assertion1SMT = "(not (and (= x (+ 5 y)) (< x!1 x!2)))"

assertion2 = Forall [x0, y0] $ Exists [x1] $ Lt (Var x1) (Var x2)
assertion2SMT = "(forall ((x int) (y int)) (exists ((x!1 int)) (< x!1 x!2)))"

assertion3 = And [And [Exists [TypedName (Name "z" 5990) Int]
                       (Imp (Atom (TypedName (Name "SC" 8875) Bool)) AFalse)]]
assertion3SMT = "(and (and (exists ((z!5990 int)) (=> SC!8875 false))))"

test_freeVars1 =
  assertEqual (Set.fromList [x0, x1, x2, y0]) (freeVars assertion1)
test_freeVars2 =
  assertEqual (Set.fromList [x2]) (freeVars assertion2)

test_toSMT1 =
  assertEqual assertion1SMT $ toSMT assertion1
test_toSMT2 =
  assertEqual assertion2SMT $ toSMT assertion2
test_toSMT3 =
  assertEqual assertion3SMT $ toSMT assertion3
test_toSMTWithNeg =
  assertEqual "(< -1 1)" $ toSMT (Lt (Num (-1)) (Num 1))

test_parseAssertion1 =
  assertEqual (Right assertion1) $ parseAssertion assertion1SMT
test_parseAssertion2 =
  assertEqual (Right assertion2) $ parseAssertion assertion2SMT
test_parseAssertion3 =
  assertEqual (Right assertion3) $ parseAssertion assertion3SMT
test_parseAssertionWithNeg =
  assertEqual (Right $ Lt (Num (-1)) (Num 1)) $ parseAssertion "(< -1 1)"

-- Doesn't seem to terminate.
--
-- prop_smtRoundTrip :: Assertion -> Bool
-- prop_smtRoundTrip assertion =
--   let smt = toSMT assertion
--   in case parseAssertion smt of
--     Left _       -> False
--     Right parsed -> smt == toSMT parsed
