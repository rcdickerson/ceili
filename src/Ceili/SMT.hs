{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Ceili.SMT
  ( SatCheckable(..)
  , SatResult(..)
  , ValidResult(..)
  , ValidCheckable(..)
  , checkSatNoLog
  , checkSatFL
  , checkValidNoLog
  , checkValidFL
  , declareVars
  ) where

import qualified Ceili.Assertion as C
import Ceili.Name
import Ceili.SMTString ( toSMT, smtTypeString )
import Control.Exception ( bracket )
import Data.ByteString ( ByteString )
import Data.ByteString.Char8 ( pack, unpack )
import Data.IORef ( newIORef, modifyIORef', readIORef )
import qualified Data.Set as Set
import qualified SimpleSMT as SSMT
import qualified System.Log.FastLogger as FL

data SatResult = Sat String | Unsat | SatUnknown | SatTimeout
data ValidResult = Valid | Invalid String | ValidUnknown | ValidTimeout

checkValidNoLog :: ValidCheckable t => C.Assertion t -> IO ValidResult
checkValidNoLog assertion = do
  logger <- SSMT.newLogger 0
  checkValid logger assertion

checkValidFL :: ValidCheckable t => FL.FastLogger -> C.Assertion t -> IO ValidResult
checkValidFL fastLogger assertion = do
  ssmtLogger <- fastLoggerAdapter fastLogger
  checkValid ssmtLogger assertion

checkSatNoLog :: SatCheckable t => C.Assertion t -> IO SatResult
checkSatNoLog assertion = do
  logger <- SSMT.newLogger 0
  checkSat logger assertion

checkSatFL :: SatCheckable t => FL.FastLogger -> C.Assertion t -> IO SatResult
checkSatFL fastLogger assertion = do
  ssmtLogger <- fastLoggerAdapter fastLogger
  checkSat ssmtLogger assertion

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

declareVars :: SSMT.Solver -> [(Name, String)] -> IO ()
declareVars solver fvs = let
  declareVars = map (\(name, typ) -> toDeclareConst name typ) fvs
  in mapM_ (SSMT.ackCommand solver) declareVars

toDeclareConst :: Name -> String -> SSMT.SExpr
toDeclareConst name typ =
  SSMT.Atom . unpack $ "(declare-const " <> C.toSMT name <> " " <> pack typ <> ")"


------------------
-- SatCheckable --
------------------

class SatCheckable t where
  checkSat :: SSMT.Logger -> C.Assertion t -> IO SatResult

instance SatCheckable Integer where
  checkSat logger assertion = do
    let fvs = Set.toList . C.freeVars $ assertion
    let typePair name = (name, unpack $ smtTypeString @Integer)
    let performCheck solver = do
          declareVars solver $ map typePair fvs
          SSMT.assert solver $ SSMT.Atom (unpack . toSMT $ assertion)
          result <- SSMT.check solver
          case result of
            SSMT.Sat -> do
              model <- SSMT.command solver $ SSMT.List [SSMT.Atom "get-model"]
              pure $ Sat $ SSMT.showsSExpr model ""
            SSMT.Unsat   -> pure Unsat
            SSMT.Unknown -> pure SatUnknown
            SSMT.Timeout -> pure SatTimeout
    bracket
      (SSMT.newSolver "z3" ["-in", "-T:2"] $ Just logger)
      (\solver -> SSMT.stop solver)
      performCheck


--------------------
-- ValidCheckable --
--------------------

class ValidCheckable t where
  checkValid :: SSMT.Logger -> C.Assertion t -> IO ValidResult

instance ValidCheckable Integer where
  checkValid logger assertion = do
    satResult <- checkSat logger $ C.Not assertion
    return $ case satResult of
      Sat model  -> Invalid model
      Unsat      -> Valid
      SatUnknown -> ValidUnknown
      SatTimeout -> ValidTimeout
