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

prog1 = impSeq [ impAsgn x $ ALit 5
               , impIf (BLt (AVar x) (ALit 0))
                       (impAsgn y $ ALit 0)
                       (impAsgn y $ ALit 1) ]

assertion assertionStr = case parseAssertion assertionStr of
  Left err        -> error $ "Bad assertion string: " ++ show err
  Right assertion -> assertion

test_forwardPT = do
  let expected = assertion
        "(or \
        \ (exists ((y!1 int)) \
        \   (and (= y 0)      \
        \        (and (exists ((x!1 int)) (and (= x 5) true)) (< x 0)))) \
        \ (exists ((y!1 int)) \
        \   (and (= y 1)      \
        \        (and (exists ((x!1 int)) (and (= x 5) true)) (not (< x 0))))))"
  actualEither <- runCeili defaultEnv $ forwardPT ATrue prog1
  case actualEither of
    Left err     -> assertFailure $ show err
    Right actual -> assertEqual expected actual

test_backwardPT = do
  let post = Eq (Var iy) (Num 1)
  let expected = assertion
        "(and \
        \  (=> (< 5 0) (= 0 1)) \
        \  (=> (not (< 5 0)) (= 1 1)))"
  actualEither <- runCeili defaultEnv $ backwardPT post prog1
  case actualEither of
    Left err     -> assertFailure $ show err
    Right actual -> assertEqual expected actual


test_mapNames = do
  let expected = impSeq [ impAsgn (Name "x!foo" 0) $ ALit 5
                        , impIf (BLt (AVar (Name "x!foo" 0)) (ALit 0))
                                (impAsgn (Name "y!foo" 0) $ ALit 0)
                                (impAsgn (Name "y!foo" 0) $ ALit 1) ]
  let actual = mapNames (\(Name n i) -> Name (n ++ "!foo") i) prog1
  assertEqual expected actual
