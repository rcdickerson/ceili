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

add2Impl :: FunImpl
add2Impl = FunImpl { fimpl_params = [x]
                   , fimpl_body = impSeq
                                  [ impCall "add1" [AVar x] [y]
                                  , impAsgn y $ AAdd (AVar y) (ALit 1)
                                  ]
                   , fimpl_returns = [y]
                   }

implEnv = Map.fromList [ ("add1", add1Impl)
                       , ("add2", add2Impl)
                       ]

prog1 :: FunImpProgram
prog1 = impSeq [ impCall "add1" [AVar x] [x]
               , impAsgn x $ AAdd (AVar x) (ALit 1)
               ]

prog2 :: FunImpProgram
prog2 = impSeq [ impCall "add2" [AVar x] [x]
               , impAsgn x $ AAdd (AVar x) (ALit 1)
               ]


test_backwardPT = do
  result <- runCeili (mkEnv prog1) $ impBackwardPT implEnv prog1 $ Eq (Var $ TypedName x Int) (Num 2)
  case result of
    Left err     -> assertFailure $ show err
    Right actual -> assertImplies actual $ Eq (Var $ TypedName x Int) (Num 0)

test_backwardPTNested = do
  result <- runCeili (mkEnv prog2) $ impBackwardPT implEnv prog2 $ Eq (Var $ TypedName x Int) (Num 3)
  case result of
    Left err     -> assertFailure $ show err
    Right actual -> assertImplies actual $ Eq (Var $ TypedName x Int) (Num 0)

test_forwardPT = do
  result <- runCeili (mkEnv prog1) $ impForwardPT implEnv prog1 $ Eq (Var $ TypedName x Int) (Num 0)
  case result of
    Left err     -> assertFailure $ show err
    Right actual -> assertImplies actual $ Eq (Var $ TypedName x Int) (Num 2)

test_forwardPTNested = do
  result <- runCeili (mkEnv prog2) $ impForwardPT implEnv prog2 $ Eq (Var $ TypedName x Int) (Num 0)
  case result of
    Left err     -> assertFailure $ show err
    Right actual -> assertImplies actual $ Eq (Var $ TypedName x Int) (Num 3)
