{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.Language.FunImpParserTest(htf_thisModulesTests) where

import Test.Framework

import Ceili.Language.FunImp
import Ceili.Language.FunImpParser
import qualified Data.Map as Map

-- Some dummy names / vars for convenience
n name = Name name 0
x = n "x"
y = n "y"

assertCorrectParse progStr expected =
  case parseFunImp progStr of
    Left err     -> assertFailure $ "Parse error: " ++ (show err)
    Right actual -> assertEqual expected actual

test_funDef = let
  prog = "fun foo(x) { x := 0; return x; }"
  expected = Map.fromList
    [("foo", FunImpl{ fimple_params = [x],
                      fimpl_body = fimpSeq [
                         fimpAsgn x (ALit 0),
                         fimpAsgn (Name "foo!retVal" 0) (AVar x)],
                      fimpl_returns = [Name "foo!retVal" 0]})]
  in assertCorrectParse prog expected

test_twoFuns = let
  prog = "fun foo(x) { x := 0; return x; } \
        \ fun bar(y) { y := 5; return y; }"
  expected = Map.fromList
    [("foo", FunImpl{ fimple_params = [x],
                      fimpl_body = fimpSeq [
                         fimpAsgn x (ALit 0),
                         fimpAsgn (Name "foo!retVal" 0) (AVar x)],
                      fimpl_returns = [Name "foo!retVal" 0]}),
     ("bar", FunImpl{ fimple_params = [y],
                      fimpl_body = fimpSeq [
                         fimpAsgn y (ALit 5),
                         fimpAsgn (Name "bar!retVal" 0) (AVar y)],
                      fimpl_returns = [Name "bar!retVal" 0]})]
  in assertCorrectParse prog expected

test_funCall = let
  prog = "fun foo(x) { x := call foo(x); return x; }"
  expected = Map.fromList
    [("foo", FunImpl{ fimple_params = [x],
                      fimpl_body = fimpSeq [
                         fimpCall "foo" [AVar x] [x],
                         fimpAsgn (Name "foo!retVal" 0) (AVar x)],
                      fimpl_returns = [Name "foo!retVal" 0]})]
  in assertCorrectParse prog expected
