{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.Language.ImpTest(htf_thisModulesTests) where
import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.Imp
import Ceili.Name

x = Name "x" 0
y = Name "y" 0
ix = TypedName x Int
iy = TypedName y Int

prog1 = SSeq [ SAsgn x $ ALit 5
             , SIf (BLt (AVar x) (ALit 0))
               (SAsgn y $ ALit 0)
               (SAsgn y $ ALit 1)
             ]

test_forwardPT = do
  let expectedE = parseAssertion $
        "(or \
        \ (exists ((y!1 int)) \
        \   (and (= y 0)      \
        \        (and (exists ((x!1 int)) (and (= x 5) true)) (< x 0)))) \
        \ (exists ((y!1 int)) \
        \   (and (= y 1)      \
        \        (and (exists ((x!1 int)) (and (= x 5) true)) (not (< x 0))))))"
  actualE <- runCeili defaultEnv $ forwardPT ATrue prog1
  case (expectedE, actualE) of
    (Left err, _)  -> assertFailure $ show err
    (_, Left err)  -> assertFailure $ show err
    (Right expected, Right actual) -> assertEqual expected actual
