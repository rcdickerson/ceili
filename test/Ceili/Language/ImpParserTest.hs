{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.Language.ImpParserTest(htf_thisModulesTests) where

import Test.Framework

import Ceili.Language.Imp
import Ceili.Language.ImpParser

-- Some dummy names / vars for convenience
n name = Name name 0
v = AVar . n
x = n "x"
y = n "y"

assertCorrectParse progStr expected = case parseImp progStr of
  Left err   -> assertFailure $ "Parse error: " ++ (show err)
  Right prog -> assertEqual expected prog

test_skip = let
  prog = "skip;"
  expected = impSkip
  in assertCorrectParse prog expected

test_asgn = let
  prog = "x := 5;"
  expected = impAsgn (n "x") (ALit 5)
  in assertCorrectParse prog expected

test_seq = let
  prog = "x := 5; y := 10;"
  expected = impSeq [ impAsgn x (ALit 5)
                  , impAsgn y (ALit 10)
                  ]
  in assertCorrectParse prog expected

test_if = let
  prog = "if x == 5 then y := 5; else y := 10; endif"
  expected = impIf (BEq (v "x") (ALit 5))
                 (impAsgn y (ALit 5))
                 (impAsgn y (ALit 10))
  in assertCorrectParse prog expected

test_ifNoElse = let
  prog = "if x == 5 then y := 5; endif"
  expected = impIf (BEq (v "x") (ALit 5))
                 (impAsgn y (ALit 5))
                 impSkip
  in assertCorrectParse prog expected

test_while = let
  prog = "while x == 5 do y := 10; end"
  expected = impWhile (BEq (v "x") (ALit 5))
                 (impAsgn y (ALit 10))
  in assertCorrectParse prog expected
