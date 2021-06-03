{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.Language.FunImpTest(htf_thisModulesTests) where
import Test.Framework

import Ceili.Assertion
import Ceili.Language.FunImp
import Ceili.Name

assertion :: String -> IO Assertion
assertion str = case parseAssertion str of
  Left err -> assertFailure $ show err
  Right a  -> return a

test_instantiateSpec = do
  pre  <- assertion "(and (>= param!1 0) (< param!1 param!2))"
  post <- assertion "(= ret (- param!2 param!1))"
  let spec = FunSpec [Name "param" 1, Name "param" 2]
                     [Name "ret" 0]
                     pre post
  let args = [Num 5, Var $ TypedName (Name "someVar" 0) Int]
  let assignees = [Name "assignee" 0]
  let (actualPre, actualPost) = instantiateSpec spec args assignees
  expectedPre  <- assertion "(and (>= 5 0) (< 5 someVar))"
  assertEqual expectedPre actualPre
  expectedPost <- assertion "(= assignee (- someVar 5))"
  assertEqual expectedPost actualPost
