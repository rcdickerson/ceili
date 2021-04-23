module Ceili.SMT
  ( SatResult(..)
  , ValidResult(..)
  , checkValid
  ) where

import qualified Ceili.Assertion as C
import Ceili.Name ( TypedName(..), Type(..) )
import Ceili.ToSMT ( toSMT )
import qualified Data.Set as Set
import qualified SimpleSMT as SSMT

data SatResult = Sat String | Unsat | SatUnknown
data ValidResult = Valid | Invalid String | ValidUnknown

checkValid :: C.Assertion -> IO ValidResult
checkValid assertion = do
  satResult <- checkSat $ C.Not assertion
  return $ case satResult of
    Sat model  -> Invalid model
    Unsat      -> Valid
    SatUnknown -> ValidUnknown

checkSat :: C.Assertion -> IO SatResult
checkSat assertion = do
    solver <- (SSMT.newSolver "z3" ["-in"]) . Just =<< SSMT.newLogger 0
    declareFVs solver assertion
    SSMT.assert solver $ toSSMT assertion
    result <- SSMT.check solver
    case result of
      SSMT.Sat -> do
        model <- SSMT.command solver $ SSMT.List [SSMT.Atom "get-model"]
        let sat = Sat $ SSMT.showsSExpr model ""
        _ <- SSMT.stop solver
        return sat
      SSMT.Unsat   -> SSMT.stop solver >> return Unsat
      SSMT.Unknown -> SSMT.stop solver >> return SatUnknown

declareFVs :: SSMT.Solver -> C.Assertion -> IO ()
declareFVs solver assertion = let
  fvs         = Set.toList $ C.freeVars assertion
  declareVars = map toDeclareConst fvs
  in mapM_ (SSMT.ackCommand solver) declareVars

toSSMT :: C.Assertion -> SSMT.SExpr
toSSMT = SSMT.Atom . toSMT

toDeclareConst :: TypedName -> SSMT.SExpr
toDeclareConst (TypedName name typ) = case typ of
  Bool -> SSMT.Atom $ "(declare-const " ++ toSMT name ++ " Bool)"
  Int  -> SSMT.Atom $ "(declare-const " ++ toSMT name ++ " Int)"
