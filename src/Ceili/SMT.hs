{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Ceili.SMT
  ( SatResult(..)
  , SMTQuery(..)
  , SMTQueryable(..)
  , ValidResult(..)
  , checkSat
  , checkSatFL
  , checkValid
  , checkValidFL
  ) where

import qualified Ceili.Assertion as C
import Ceili.Name
import Ceili.SMTString ( toSMT, smtTypeString )
import Data.ByteString ( ByteString )
import Data.ByteString.Char8 ( pack, unpack )
import Data.IORef ( newIORef, modifyIORef', readIORef )
import qualified Data.Set as Set
import qualified SimpleSMT as SSMT
import qualified System.Log.FastLogger as FL

data SatResult = Sat String | Unsat | SatUnknown
data ValidResult = Valid | Invalid String | ValidUnknown

checkValid :: SMTQueryable t
           => C.Assertion t -> IO ValidResult
checkValid assertion = do
  logger <- SSMT.newLogger 0
  checkValidWithLogger logger assertion

checkValidFL :: SMTQueryable t
             => FL.FastLogger -> C.Assertion t -> IO ValidResult
checkValidFL fastLogger assertion = do
  ssmtLogger <- fastLoggerAdapter fastLogger
  checkValidWithLogger ssmtLogger assertion

checkValidWithLogger :: SMTQueryable t
                     => SSMT.Logger -> C.Assertion t -> IO ValidResult
checkValidWithLogger logger assertion = do
  satResult <- checkSatWithLogger logger $ C.Not assertion
  return $ case satResult of
    Sat model  -> Invalid model
    Unsat      -> Valid
    SatUnknown -> ValidUnknown

checkSat :: SMTQueryable t
         => C.Assertion t -> IO SatResult
checkSat assertion = do
  logger <- SSMT.newLogger 0
  checkSatWithLogger logger assertion

checkSatFL :: SMTQueryable t
           => FL.FastLogger -> C.Assertion t -> IO SatResult
checkSatFL fastLogger assertion = do
  ssmtLogger <- fastLoggerAdapter fastLogger
  checkSatWithLogger ssmtLogger assertion

checkSatWithLogger :: SMTQueryable t
                   => SSMT.Logger
                   -> C.Assertion t
                   -> IO SatResult
checkSatWithLogger logger assertion = do
  let (SMTQuery fvs query) = buildSMTQuery $ assertion
  solver <- (SSMT.newSolver "z3" ["-in"]) $ Just logger
  declareFVs solver fvs
  SSMT.assert solver $ SSMT.Atom query
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
        let indent = FL.toLogStr $ replicate tabs ' '
        fastLogger $ indent <> FL.toLogStr msg <> FL.toLogStr @ByteString "\n"
    , SSMT.logLevel    = return 0
    , SSMT.logSetLevel = \_ -> return ()
    , SSMT.logTab      = modifyIORef' tab (+ 2)
    , SSMT.logUntab    = modifyIORef' tab (subtract 2)
    }

declareFVs :: SSMT.Solver -> [(Name, String)] -> IO ()
declareFVs solver fvs = let
  declareVars = map (\(name, typ) -> toDeclareConst name typ) fvs
  in mapM_ (SSMT.ackCommand solver) declareVars

toDeclareConst :: Name -> String -> SSMT.SExpr
toDeclareConst name typ =
  SSMT.Atom . unpack $ "(declare-const " <> C.toSMT name <> " " <> pack typ <> ")"


--------------------
-- Query Building --
--------------------

data SMTQuery = SMTQuery { smtq_vars  :: [(Name, String)]
                         , smtq_query :: String
                         }

class SMTQueryable t where
  buildSMTQuery :: C.Assertion t -> SMTQuery

instance SMTQueryable Integer where
  buildSMTQuery assertion =
    let
      fvs = Set.toList . C.freeVars $ assertion
      typePair name = (name, unpack $ smtTypeString @Integer)
    in SMTQuery (map typePair fvs) (unpack . toSMT $ assertion)
