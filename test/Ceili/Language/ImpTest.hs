{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.Language.ImpTest(htf_thisModulesTests) where
import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.Imp
import Ceili.Name
import qualified Data.Map as Map

name n = Name n 0
x = name "x"
y = name "y"
ix = TypedName x Int
iy = TypedName y Int
mkSt assocList = Map.fromList $ map (\(n,v) -> (Name n 0, v)) assocList

prog1 :: ImpProgram
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
  actualEither <- runCeili defaultEnv $ impForwardPT prog1 ATrue
  case actualEither of
    Left err     -> assertFailure $ show err
    Right actual -> assertEqual expected actual

test_backwardPT = do
  let post = Eq (Var iy) (Num 1)
  let expected = assertion
        "(and \
        \  (=> (< 5 0) (= 0 1)) \
        \  (=> (not (< 5 0)) (= 1 1)))"
  actualEither <- runCeili defaultEnv $ impBackwardPT prog1 post
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

test_evalImp_Skip = let
  st = mkSt [("x", 1), ("y", 2)]
  in assertEqual (Just st) $ evalImp st InfiniteFuel (impSkip :: ImpProgram)

test_evalImp_Asgn = let
  st = mkSt [("x", 1), ("y", 2)]
  prog = (impAsgn x $ AAdd (AVar y) (ALit 3)) :: ImpProgram
  expected = mkSt [("x", 5), ("y", 2)]
  in assertEqual (Just expected) $ evalImp st InfiniteFuel prog

test_evalImp_Seq = let
  st = mkSt [("x", 1), ("y", 2)]
  prog = (impSeq [ impSkip
                 , impAsgn y $ ALit 7
                 , impAsgn x $ ASub (AVar y) (ALit 5)
                 ]) :: ImpProgram
  expected = mkSt [("x", 2), ("y", 7)]
  in assertEqual (Just expected) $ evalImp st InfiniteFuel prog

test_evalImp_IfTrue = let
  st = mkSt [("x", 1), ("y", -1)]
  prog = (impIf (BGt (AVar x) (ALit 0))
                (impAsgn y $ ALit 1)
                (impAsgn y $ ALit 0)) :: ImpProgram
  expected = mkSt [("x", 1), ("y", 1)]
  in assertEqual (Just expected) $ evalImp st InfiniteFuel prog

test_evalImp_IfFalse = let
  st = mkSt [("x", 1), ("y", -1)]
  prog = (impIf (BLt (AVar x) (ALit 0))
                (impAsgn y $ ALit 1)
                (impAsgn y $ ALit 0)) :: ImpProgram
  expected = mkSt [("x", 1), ("y", 0)]
  in assertEqual (Just expected) $ evalImp st InfiniteFuel prog

test_evalImp_WhileFalse = let
  st = mkSt [("x", 11), ("y", 0)]
  prog = (impWhile (BLt (AVar x) (ALit 10))
                   (impSeq [ impAsgn y (ALit 1)
                           , impAsgn x $ AAdd (AVar x) (ALit 1)
                           ])) :: ImpProgram
  expected = mkSt [("x", 11), ("y", 0)]
  in assertEqual (Just expected) $ evalImp st InfiniteFuel prog

test_evalImp_WhileLoop = let
  st = mkSt [("x", 0), ("y", 0)]
  prog = (impWhile (BLt (AVar x) (ALit 10))
                   (impSeq [ impAsgn y (ALit 1)
                           , impAsgn x $ AAdd (AVar x) (ALit 1)
                           ])) :: ImpProgram
  expected = mkSt [("x", 10), ("y", 1)]
  in assertEqual (Just expected) $ evalImp st InfiniteFuel prog

test_evalImp_InfiniteLoopRunsOutOfFuel = let
  prog = (impWhile BTrue impSkip) :: ImpProgram
  in assertEqual Nothing $ evalImp Map.empty (Fuel 100) prog

test_evalImp_slowMult = let
  st = mkSt [("x", 5), ("y", 7)]
  z  = name "z"
  c  = name "c"
  prog = (impSeq [ impAsgn c $ AVar x
                 , impAsgn z (ALit 0)
                 , impWhile (BGt (AVar c) (ALit 0))
                            (impSeq [ impAsgn z $ AAdd (AVar z) (AVar y)
                                    , impAsgn c $ ASub (AVar c) (ALit 1)
                                    ])
                 ]) :: ImpProgram
  expected = mkSt [("x", 5), ("y", 7), ("c", 0), ("z", 35)]
  in assertEqual (Just expected) $ evalImp st (Fuel 100) prog
