{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.Language.ImpParserTest(htf_thisModulesTests) where

import Test.Framework

import Ceili.Language.Imp
import Ceili.Language.ImpParser

-- Some dummy names / vars for convenience
n name = Name name 0
v = AVar . n
a = v "a"
b = v "b"
c = v "c"
x = n "x"
y = n "y"
z = n "z"

assertCorrectParse progStr expected = case parseImp progStr of
  Left err   -> assertFailure $ "Parse error: " ++ (show err)
  Right prog -> assertEqual expected prog

test_emptyProg = let
  prog = "skip;"
  expected = SSkip
  in assertCorrectParse prog expected
