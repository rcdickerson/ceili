{-# OPTIONS_GHC -F -pgmF htfpp #-}
module Ceili.ImpVerificationTests(htf_thisModulesTests) where

import Test.Framework

import Ceili.Assertion ( Arith(..), Assertion(..) )
import Ceili.CeiliEnv
import Ceili.Language.Imp
import Ceili.Language.ImpParser
import Ceili.Name
import qualified Ceili.SMT as SMT
import qualified Data.Map as Map
import qualified Data.Set as Set
import System.FilePath

data ExpectResult = ExpectSuccess | ExpectFailure

assertSMTResult expected result =
  case (expected, result) of
    (ExpectSuccess, SMT.Valid) -> return ()
    (ExpectFailure, SMT.Invalid _) -> return ()
    (ExpectSuccess, SMT.Invalid msg) -> assertFailure
      $ "Expected VALID but was INVALID. Message: " ++ msg
    (ExpectFailure, SMT.Valid) -> assertFailure
      $ "Expected INVALID but was VALID"
    _ -> assertFailure "Unknown SMT result"

assertRunsWithoutErrors task check = do
  spOrErr <- runCeili defaultEnv $ task
  case spOrErr of
    Left err     -> assertFailure $ show err
    Right result -> check result

assertRunsWithError task expectedErr = do
  spOrErr <- runCeili defaultEnv $ task
  case spOrErr of
    Left err     -> assertEqual expectedErr err
    Right result -> assertFailure $ "Unexpected success: " ++ show result

readImpFile fileName = do
  readFile $ "verification-test"
         </> "resources"
         </> "imp"
         </> fileName

readAndParse path = do
  progStr <- readImpFile path
  case parseImp progStr of
    Left  err     -> assertFailure $ "Parse error: " ++ (show err)
    Right program -> return program


varX = Var $ TypedName (Name "x" 0) Int
varY = Var $ TypedName (Name "y" 0) Int

mkTestStartStates :: CollectableNames n => n -> [State]
mkTestStartStates cnames =
  let names = Set.toList $ namesIn cnames
  in [ Map.fromList $ map (\n -> (n, 0)) names
     , Map.fromList $ map (\n -> (n, 1)) names
     , Map.fromList $ map (\n -> (n, -1)) names
     ]


test_forwardInferInv1Valid = do
  let post = Eq varX varY
  prog <- readAndParse "inferInv1.imp"
  assertRunsWithoutErrors (forwardPT ATrue prog) $
    \result -> do
      smtResult <- SMT.checkValid $ Imp result post
      assertSMTResult ExpectSuccess smtResult

test_forwardInferInv1Invalid = do
  let post = Not $ Eq varX varY
  prog <- readAndParse "inferInv1.imp"
  assertRunsWithoutErrors (forwardPT ATrue prog) $
    \result -> do
      smtResult <- SMT.checkValid $ Imp result post
      assertSMTResult ExpectFailure smtResult

test_backwardInferInv1Valid = do
  let post = Eq varX varY
  prog <- readAndParse "inferInv1.imp"
  let progWithTests = populateTestStates (mkTestStartStates prog)
                                         (Fuel 1000)
                                         prog
  assertRunsWithoutErrors (backwardPT post progWithTests) $
    \result -> do
      smtResult <- SMT.checkValid result
      assertSMTResult ExpectSuccess smtResult

test_backwardInferInv1Invalid = do
  let post = Not $ Eq varX varY
  prog <- readAndParse "inferInv1.imp"
  let progWithTests = populateTestStates (mkTestStartStates prog)
                                         (Fuel 1000)
                                         prog
  assertRunsWithError (backwardPT post progWithTests) "Unable to infer loop invariant."
