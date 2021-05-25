{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.Language.AExpTest(htf_thisModulesTests) where
import Test.Framework

import Ceili.Language.AExp
import Ceili.Name
import qualified Data.Map as Map

mkSt assocList = Map.fromList $ map (\(n,v) -> (Name n 0, v)) assocList
name n = Name n 0

test_evalAExp_Lit = do
  assertEqual 0    $ evalAExp Map.empty (ALit 0)
  assertEqual 1    $ evalAExp Map.empty (ALit 1)
  assertEqual (-1) $ evalAExp Map.empty (ALit $ -1)

test_evalAExp_Var = do
  assertEqual 0    $ evalAExp (mkSt [("x", 0)])  (AVar $ name "x")
  assertEqual 1    $ evalAExp (mkSt [("y", 1)])  (AVar $ name "y")
  assertEqual (-1) $ evalAExp (mkSt [("z", -1)]) (AVar $ name "z")

test_evalAExp_defaultsToZero = do
  assertEqual 0 $ evalAExp Map.empty (AVar $ name "x")

test_evalAExp_MiscArith = do
  assertEqual 10   $ evalAExp
                     Map.empty
                     (AAdd (ASub (ALit 5) (ALit 3))
                           (AMul (ALit 2) (ALit 4)))
  assertEqual (-1) $ evalAExp
                     (mkSt [("x", 0), ("y", 3)])
                     (ASub (AVar $ name "x")
                           (AMod (ALit 13) (AVar $ name "y")))
  assertEqual 9    $ evalAExp
                     (mkSt [("x", 10), ("y", 3)])
                     (APow (AVar $ name "y")
                           (ADiv (ALit 21) (AVar $ name "x")))
