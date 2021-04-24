{-# OPTIONS_GHC -F -pgmF htfpp #-}
module VerificationTestMain where

import Test.Framework

import Ceili.Assertion ( Arith(..), Assertion(..) )
import qualified Ceili.Language.Imp as Imp
import Ceili.Language.ImpParser
import Ceili.Name
import qualified Ceili.SMT as SMT
import System.FilePath

main = htfMain htf_thisModulesTests

data ExpectResult = ExpectSuccess | ExpectFailure

assertVerifierResultMatches expected result =
  case (expected, result) of
    (ExpectSuccess, SMT.Valid) -> return ()
    (ExpectFailure, SMT.Invalid _) -> return ()
    (ExpectSuccess, SMT.Invalid msg) -> assertFailure
      $ "Expected VALID but was INVALID. Message: " ++ msg
    (ExpectFailure, SMT.Valid) -> assertFailure
      $ "Expected INVALID but was VALID"

parseAndTest pre progStr post expected = case parseImp progStr of
  Left  err     -> assertFailure $ "Parse error: " ++ (show err)
  Right program -> do
    sp <- Imp.forwardPT pre program
    result <- SMT.checkValid $ Imp sp post
    assertVerifierResultMatches expected result

readImpFile fileName = do
  readFile $ "verification-test"
         </> "resources"
         </> "imp"
         </> fileName

test_inferInv1 = do
  let post = Eq (Var $ TypedName (Name "x" 0) Int)
                (Var $ TypedName (Name "y" 0) Int)
  progStr <- readImpFile "inferInv1.imp"
  parseAndTest ATrue progStr post ExpectSuccess
