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
sc8875 = TypedName (Name "SC" 8875) Bool


assertion1 = Not $ And [ Eq (Var x0) (Add [Num 5, Var y0])
                       , Lt (Var x1) (Var x2)
                       ]
assertion1SMT = "(not (and (= x (+ 5 y)) (< x!1 x!2)))"

assertion2 = Forall [x0, y0] $ Exists [x1] $ Lt (Var x1) (Var x2)
assertion2SMT = "(forall ((x int) (y int)) (exists ((x!1 int)) (< x!1 x!2)))"

assertion3 = And [And [Exists [TypedName (Name "z" 5990) Int]
                       (Imp (Atom sc8875) AFalse)]]
assertion3SMT = "(and (and (exists ((z!5990 int)) (=> SC!8875 false))))"

test_freeVars = do
  assertEqual (Set.fromList [x0, x1, x2, y0]) (freeVars assertion1)
  assertEqual (Set.fromList [x2]) (freeVars assertion2)

test_toSMT = do
  assertEqual assertion1SMT $ toSMT assertion1
  assertEqual assertion2SMT $ toSMT assertion2
  assertEqual assertion3SMT $ toSMT assertion3
  assertEqual "(< -1 1)" $ toSMT (Lt (Num (-1)) (Num 1))

test_parseAssertion = do
  assertEqual (Right assertion1) $ parseAssertion assertion1SMT
  assertEqual (Right assertion2) $ parseAssertion assertion2SMT
  assertEqual (Right assertion3) $ parseAssertion assertion3SMT
  assertEqual (Right $ Lt (Num (-1)) (Num 1)) $ parseAssertion "(< -1 1)"

test_subArith = do
  assertEqual ( Not $ And [ Eq (Add [Var x0, Num 1]) (Add [Num 5, Var y0])
                       , Lt (Var x1) (Var x2)] )
              ( subArith x0 (Add [ Var x0, Num 1 ]) assertion1 )
  assertEqual ( Forall [x0, y0] $ Exists [x1] $ Lt (Var x1) (Var x2) )
              ( subArith x0 (Add [ Var x0, Num 1 ]) assertion2 )
  assertEqual ( And [And [Exists [TypedName (Name "z" 5990) Int]
                       (Imp (Atom sc8875) AFalse)]])
              ( subArith sc8875 (Add [ Var x0, Num 1 ]) assertion3 )
  let assertion3' = And [And [Exists [TypedName (Name "z" 5990) Int]
                       (Imp (Eq (Var x0) (Var x1)) AFalse)]]
  assertEqual ( And [And [Exists [TypedName (Name "z" 5990) Int]
                       (Imp (Eq (Add [Var x0, Num 1]) (Var x1)) AFalse)]])
              ( subArith x0 (Add [ Var x0, Num 1 ]) assertion3' )
