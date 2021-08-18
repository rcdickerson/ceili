{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.InvariantInference.PieVerificationTests(htf_thisModulesTests) where

import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.InvariantInference.Pie
import Ceili.Language.BExp ( bexpToAssertion )
import Ceili.Language.Imp
import Ceili.Literal
import Ceili.Name
import qualified Ceili.SMT as SMT
import qualified Data.Set as Set
import System.Log.FastLogger

env :: ImpProgram -> Assertion -> Env
env prog post = defaultEnv names lits
  where
    names = Set.union (typedNamesIn prog) (typedNamesIn post)
    lits  = Set.union (litsIn prog) (litsIn post)

assertEquivalent :: Assertion -> Assertion -> IO ()
assertEquivalent a1 a2 = do
  let iff = And [ Imp a1 a2, Imp a2 a1 ]
  result <- withFastLogger LogNone $ \logger ->
            SMT.checkValidFL logger iff
  case result of
    SMT.Valid        -> return () -- pass
    SMT.Invalid s    -> assertFailure s
    SMT.ValidUnknown -> assertFailure "Unable to establish equivalence."

runAndAssertEquivalent :: Env -> Assertion -> Ceili (Maybe Assertion) -> IO ()
runAndAssertEquivalent env expected actual = do
  result <- runCeili env actual
  case result of
    Left err         -> assertFailure err
    Right mAssertion ->
      case mAssertion of
        Nothing     -> assertFailure "Expected assertion, got Nothing."
        Just actual -> assertEquivalent expected actual

-- This is the "Slow Subtraction" example from Software Foundations, Pierce et al.
-- https://softwarefoundations.cis.upenn.edu/plf-current/Hoare2.html
test_loopInvGen = let
  x = Name "x" 0
  y = Name "y" 0
  n = Name "n" 0
  m = Name "m" 0
  tn n = TypedName n Int
  var n = Var $ tn n
  cond = BNe (AVar x) (ALit 0)
  body = (impSeq [ impAsgn y $ ASub (AVar y) (ALit 1)
                 , impAsgn x $ ASub (AVar x) (ALit 1)]) :: ImpProgram
  post = (Eq (var y) (Sub [var n, var m]))
  -- Loop will always start in a state where x = m and y = n.
  tests = [ And [ Eq (var x) (Num 0)
                , Eq (var y) (Num 0)
                , Eq (var m) (Num 0)
                , Eq (var n) (Num 0)]
          , And [ Eq (var x) (Num 5)
                , Eq (var y) (Num 3)
                , Eq (var m) (Num 5)
                , Eq (var n) (Num 3)]
          , And [ Eq (var x) (Num 3)
                , Eq (var y) (Num 5)
                , Eq (var m) (Num 3)
                , Eq (var n) (Num 5)]
          ]
  expected = Eq (Sub [var y, var x])
                (Sub [var n, var m])
  in runAndAssertEquivalent (env body post) expected
     $ loopInvGen impBackwardPT () (bexpToAssertion cond) body post tests
