{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Ceili.SMT
  ( SatResult(..)
  , ValidResult(..)
  , checkSat
  , checkSatFL
  , checkValid
  , checkValidFL
  ) where

import qualified Ceili.Assertion as C
import Ceili.Name
import Ceili.SMTString ( SMTString(..), SMTTypeString(..) )
import Data.ByteString ( ByteString )
import Data.ByteString.Char8 ( unpack )
import Data.IORef ( newIORef, modifyIORef', readIORef )
import qualified Data.Set as Set
import qualified SimpleSMT as SSMT
import qualified System.Log.FastLogger as FL

data SatResult = Sat String | Unsat | SatUnknown
data ValidResult = Valid | Invalid String | ValidUnknown

checkValid :: (SMTString t, SMTTypeString t)
           => C.Assertion t -> IO ValidResult
checkValid assertion = do
  logger <- SSMT.newLogger 0
  checkValidWithLogger logger assertion

checkValidFL :: (SMTString t, SMTTypeString t)
             => FL.FastLogger -> C.Assertion t -> IO ValidResult
checkValidFL fastLogger assertion = do
  ssmtLogger <- fastLoggerAdapter fastLogger
  checkValidWithLogger ssmtLogger assertion

checkValidWithLogger :: (SMTString t, SMTTypeString t)
                     => SSMT.Logger -> C.Assertion t -> IO ValidResult
checkValidWithLogger logger assertion = do
  satResult <- checkSatWithLogger logger $ C.Not assertion
  return $ case satResult of
    Sat model  -> Invalid model
    Unsat      -> Valid
    SatUnknown -> ValidUnknown

checkSat :: (SMTString t, SMTTypeString t)
         => C.Assertion t -> IO SatResult
checkSat assertion = do
  logger <- SSMT.newLogger 0
  checkSatWithLogger logger assertion

checkSatFL :: (SMTString t, SMTTypeString t)
           => FL.FastLogger -> C.Assertion t -> IO SatResult
checkSatFL fastLogger assertion = do
  ssmtLogger <- fastLoggerAdapter fastLogger
  checkSatWithLogger ssmtLogger assertion

checkSatWithLogger :: (SMTString t, SMTTypeString t)
                   => SSMT.Logger -> C.Assertion t -> IO SatResult
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
        let indent = FL.toLogStr $ replicate tabs ' '
        fastLogger $ indent <> FL.toLogStr msg <> FL.toLogStr @ByteString "\n"
    , SSMT.logLevel    = return 0
    , SSMT.logSetLevel = \_ -> return ()
    , SSMT.logTab      = modifyIORef' tab (+ 2)
    , SSMT.logUntab    = modifyIORef' tab (subtract 2)
    }

declareFVs :: forall t. (SMTString t, SMTTypeString t)
           => SSMT.Solver -> C.Assertion t -> IO ()
declareFVs solver assertion = let
  fvs         = Set.toList $ C.freeVars assertion
  typeStr     = smtTypeString @t
  declareVars = map (\n -> toDeclareConst n typeStr) fvs
  in mapM_ (SSMT.ackCommand solver) declareVars

toSSMT :: (SMTString t, SMTTypeString t) => C.Assertion t -> SSMT.SExpr
toSSMT = SSMT.Atom . unpack . toSMT

toDeclareConst :: Name -> ByteString -> SSMT.SExpr
toDeclareConst name typ =
  SSMT.Atom . unpack $ "(declare-const " <> toSMT name <> " " <> typ <> ")"
