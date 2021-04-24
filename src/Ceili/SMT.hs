module Ceili.SMT
  ( SatResult(..)
  , ValidResult(..)
  , checkSat
  , checkSatFL
  , checkValid
  , checkValidFL
  ) where

import qualified Ceili.Assertion as C
import Ceili.Name ( TypedName(..), Type(..) )
import Ceili.SMTString ( showSMT )
import Data.IORef ( newIORef, modifyIORef', readIORef )
import qualified Data.Set as Set
import qualified SimpleSMT as SSMT
import qualified System.Log.FastLogger as FL

data SatResult = Sat String | Unsat | SatUnknown
data ValidResult = Valid | Invalid String | ValidUnknown

checkValid :: C.Assertion -> IO ValidResult
checkValid assertion = do
  logger <- SSMT.newLogger 0
  checkValidWithLogger logger assertion

checkValidFL :: FL.FastLogger -> C.Assertion -> IO ValidResult
checkValidFL fastLogger assertion = do
  ssmtLogger <- fastLoggerAdapter fastLogger
  checkValidWithLogger ssmtLogger assertion

checkValidWithLogger :: SSMT.Logger -> C.Assertion -> IO ValidResult
checkValidWithLogger logger assertion = do
  satResult <- checkSatWithLogger logger $ C.Not assertion
  return $ case satResult of
    Sat model  -> Invalid model
    Unsat      -> Valid
    SatUnknown -> ValidUnknown

checkSat :: C.Assertion -> IO SatResult
checkSat assertion = do
  logger <- SSMT.newLogger 0
  checkSatWithLogger logger assertion

checkSatFL :: FL.FastLogger -> C.Assertion -> IO SatResult
checkSatFL fastLogger assertion = do
  ssmtLogger <- fastLoggerAdapter fastLogger
  checkSatWithLogger ssmtLogger assertion

checkSatWithLogger :: SSMT.Logger -> C.Assertion -> IO SatResult
checkSatWithLogger logger assertion = do
    solver <- (SSMT.newSolver "z3" ["-in"]) $ Just logger
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

fastLoggerAdapter :: FL.FastLogger -> IO SSMT.Logger
fastLoggerAdapter fastLogger = do
  tab <- newIORef 0
  return $ SSMT.Logger
    { SSMT.logMessage = \msg -> do
        tabs <- readIORef tab
        let ls   = lines msg
        let msg' = unlines [ replicate tabs ' ' ++ l | l <- ls ] -- TODO: Something more efficient
        fastLogger $ FL.toLogStr msg'
    , SSMT.logLevel    = return 0
    , SSMT.logSetLevel = \_ -> return ()
    , SSMT.logTab      = modifyIORef' tab (+ 2)
    , SSMT.logUntab    = modifyIORef' tab (subtract 2)
    }

declareFVs :: SSMT.Solver -> C.Assertion -> IO ()
declareFVs solver assertion = let
  fvs         = Set.toList $ C.freeVars assertion
  declareVars = map toDeclareConst fvs
  in mapM_ (SSMT.ackCommand solver) declareVars

toSSMT :: C.Assertion -> SSMT.SExpr
toSSMT = SSMT.Atom . showSMT

toDeclareConst :: TypedName -> SSMT.SExpr
toDeclareConst (TypedName name typ) = case typ of
  Bool -> SSMT.Atom $ "(declare-const " ++ showSMT name ++ " Bool)"
  Int  -> SSMT.Atom $ "(declare-const " ++ showSMT name ++ " Int)"
