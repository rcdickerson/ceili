{-# OPTIONS_GHC -F -pgmF htfpp #-}
module Ceili.ImpVerificationTests(htf_thisModulesTests) where

import Test.Framework

import Ceili.Assertion ( Arith(..), Assertion(..) )
import Ceili.CeiliEnv
import qualified Ceili.Language.Imp as Imp
import Ceili.Language.ImpParser
import Ceili.Name
import Ceili.PTS.BackwardPT ( backwardPT )
import Ceili.PTS.ForwardPT ( forwardPT )
import qualified Ceili.SMT as SMT
import System.FilePath
data ExpectResult = ExpectSuccess | ExpectFailure

assertVerifierResultMatches expected result =
  case (expected, result) of
    (ExpectSuccess, SMT.Valid) -> return ()
    (ExpectFailure, SMT.Invalid _) -> return ()
    (ExpectSuccess, SMT.Invalid msg) -> assertFailure
      $ "Expected VALID but was INVALID. Message: " ++ msg
    (ExpectFailure, SMT.Valid) -> assertFailure
      $ "Expected INVALID but was VALID"

parseAndTest pre progStr post predTrans expected = case parseImp progStr of
  Left  err     -> assertFailure $ "Parse error: " ++ (show err)
  Right program -> do
    spOrErr <- runCeili defaultEnv $ predTrans pre program
    case spOrErr of
      Left err     -> assertFailure $ show err
      Right sp -> do
        result <- SMT.checkValid $ Imp sp post
        assertVerifierResultMatches expected result

readImpFile fileName = do
  readFile $ "verification-test"
         </> "resources"
         </> "imp"
         </> fileName

varX = Var $ TypedName (Name "x" 0) Int
varY = Var $ TypedName (Name "y" 0) Int

test_forwardInferInv1Valid = do
  let post = Eq varX varY
  progStr <- readImpFile "inferInv1.imp"
  parseAndTest ATrue progStr post forwardPT ExpectSuccess

test_forwardInferInv1Invalid = do
  let post = Not $ Eq varX varY
  progStr <- readImpFile "inferInv1.imp"
  parseAndTest ATrue progStr post forwardPT ExpectFailure

test_backwardInferInv1Valid = do
  let post = Eq varX varY
  progStr <- readImpFile "inferInv1.imp"
  parseAndTest ATrue progStr post backwardPT ExpectSuccess

test_backwardInferInv1Invalid = do
  let post = Not $ Eq varX varY
  progStr <- readImpFile "inferInv1.imp"
  parseAndTest ATrue progStr post backwardPT ExpectFailure
