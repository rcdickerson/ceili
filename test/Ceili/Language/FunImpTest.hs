{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.Language.FunImpTest(htf_thisModulesTests) where

import Ceili.TestUtil
import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.FunImp
import Ceili.Name
import qualified Data.Map as Map


x = Name "x" 0
y = Name "y" 0

add1Impl :: FunImpl
add1Impl = FunImpl { fimpl_params = [x]
                   , fimpl_body = impAsgn y $ AAdd (AVar x) (ALit 1)
                   , fimpl_returns = [y]
                   }

prog1 :: FunImpProgram
prog1 = impSeq [ impCall "add1" [AVar x] [x]
               , impAsgn x $ AAdd (AVar x) (ALit 1)
               ]


test_backwardPT = do
  let impls = Map.fromList [("add1", add1Impl)]
  let expected = Eq (Var $ TypedName x Int) (Num 0)
  actualEither <- runCeili (mkEnv prog1) $ impBackwardPT impls prog1 $ Eq (Var $ TypedName x Int) (Num 2)
  case actualEither of
    Left err     -> assertFailure $ show err
    Right actual -> assertImplies actual expected

test_forwardPT = do
  let impls = Map.fromList [("add1", add1Impl)]
  let expected = Eq (Var $ TypedName x Int) (Num 2)
  actualEither <- runCeili (mkEnv prog1) $ impForwardPT impls prog1 $ Eq (Var $ TypedName x Int) (Num 0)
  case actualEither of
    Left err     -> assertFailure $ show err
    Right actual -> assertImplies actual expected
