module Ceili.CeiliEnv
  ( Env(..)
  , Ceili
  , LogLevel(..)
  , checkSat
  , checkSatB
  , checkSatWithLog
  , checkValid
  , checkValidB
  , checkValidWithLog
  , defaultEnv
  , emptyEnv
  , envFreshen
  , findCounterexample
  , log_d
  , log_e
  , log_i
  , mkEnv
  , runCeili
  , throwError
  ) where

import Ceili.Assertion ( Assertion(..), AssertionParseable, parseAssertion )
import Ceili.Name
import qualified Ceili.SMT as SMT
import Ceili.SMTString
import Control.Concurrent.Timeout ( timeout )
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Except ( ExceptT, runExceptT, throwError )
import Control.Monad.Trans.State ( StateT, evalStateT, get, put )
import Data.Set ( Set )
import qualified Data.Set as Set
import System.Log.FastLogger

data Env = Env { env_logger_debug :: LogType
               , env_logger_error :: LogType
               , env_logger_info  :: LogType
               , env_nextFreshIds :: NextFreshIds
               , env_smtTimeoutMs :: Integer }

data LogLevel = LogLevelDebug
              | LogLevelInfo
              | LogLevelError
              | LogLevelNone

type Ceili = StateT Env (ExceptT String IO)

runCeili :: Env -> Ceili a -> IO (Either String a)
runCeili env task = runExceptT (evalStateT task env)

mkEnv :: LogLevel -> Integer -> Set Name -> Env
mkEnv minLogLevel smtTimeoutMs names =
  Env { env_logger_debug = mkDebugLogType minLogLevel
      , env_logger_info  = mkInfoLogType minLogLevel
      , env_logger_error = mkErrorLogType minLogLevel
      , env_nextFreshIds = buildFreshIds names
      , env_smtTimeoutMs = smtTimeoutMs }

defaultEnv :: Set Name -> Env
defaultEnv = mkEnv LogLevelInfo 2000

emptyEnv :: Env
emptyEnv = defaultEnv Set.empty

mkDebugLogType :: LogLevel -> LogType
mkDebugLogType minLevel = case minLevel of
  LogLevelDebug -> LogStdout defaultBufSize
  _ -> LogNone

mkInfoLogType :: LogLevel -> LogType
mkInfoLogType minLevel = case minLevel of
  LogLevelDebug -> LogStdout defaultBufSize
  LogLevelInfo  -> LogStdout defaultBufSize
  _ -> LogNone

mkErrorLogType :: LogLevel -> LogType
mkErrorLogType minLevel = case minLevel of
  LogLevelDebug -> LogStderr defaultBufSize
  LogLevelInfo  -> LogStderr defaultBufSize
  LogLevelError -> LogStderr defaultBufSize
  _ -> LogNone

logAt :: ToLogStr m => (Env -> LogType) -> m -> Ceili ()
logAt logger message = do
  let messageLS = (toLogStr message) <> toLogStr "\n"
  logType <- get >>= return . logger
  liftIO $ withFastLogger logType ($ messageLS)

log_d :: ToLogStr m => m -> Ceili ()
log_d = logAt env_logger_debug

log_i :: ToLogStr m => m -> Ceili ()
log_i = logAt env_logger_info

log_e :: ToLogStr m => m -> Ceili ()
log_e = logAt env_logger_error

logTypeAt :: LogLevel -> Ceili LogType
logTypeAt level = case level of
  LogLevelNone  -> return LogNone
  LogLevelDebug -> get >>= return . env_logger_debug
  LogLevelError -> get >>= return . env_logger_error
  LogLevelInfo  -> get >>= return . env_logger_info

withTimeout :: IO a -> Ceili (Maybe a)
withTimeout t = do
  timeoutMs <- get >>= return . env_smtTimeoutMs
  liftIO $ timeout (1000 * timeoutMs) t

checkValid :: SMTString t => Assertion t -> Ceili SMT.ValidResult
checkValid = checkValidWithLog LogLevelDebug

checkValidB :: SMTString t => Assertion t -> Ceili Bool
checkValidB assertion = do
  valid <- checkValid assertion
  case valid of
    SMT.Valid        -> return True
    SMT.Invalid _    -> return False
    SMT.ValidUnknown -> return False

checkValidWithLog :: SMTString t => LogLevel -> Assertion t -> Ceili SMT.ValidResult
checkValidWithLog level assertion = do
  result  <- runWithLog level $ (\logger -> SMT.checkValidFL logger assertion)
  case result of
    Nothing -> do log_e "SMT timeout"; return SMT.ValidUnknown
    Just r  -> return r

checkSat :: SMTString t => Assertion t -> Ceili SMT.SatResult
checkSat = checkSatWithLog LogLevelDebug

checkSatB :: SMTString t => Assertion t -> Ceili Bool
checkSatB assertion = do
  sat <- checkSat assertion
  case sat of
    SMT.Sat _      -> return True
    SMT.Unsat      -> return False
    SMT.SatUnknown -> return False

checkSatWithLog :: SMTString t => LogLevel -> Assertion t -> Ceili SMT.SatResult
checkSatWithLog level assertion = do
  result <- runWithLog level $ (\logger -> SMT.checkSatFL logger assertion)
  case result of
    Nothing -> do log_e "SMT timeout"; return SMT.SatUnknown
    Just r  -> return r

runWithLog :: LogLevel -> (FastLogger -> IO a) -> Ceili (Maybe a)
runWithLog level task = do
  logType <- logTypeAt level
  withTimeout $
    withFastLogger logType $ \logger ->
    task logger

findCounterexample :: (AssertionParseable t, SMTString t) => Assertion t -> Ceili (Maybe (Assertion t))
findCounterexample assertion = do
  logType <- logTypeAt LogLevelDebug
  result <- withTimeout $
            withFastLogger logType $ \logger ->
            SMT.checkValidFL logger assertion
  case result of
    Nothing                  -> do log_e "SMT timeout"; return Nothing
    Just SMT.Valid           -> return Nothing
    Just SMT.ValidUnknown    -> do log_e "SMT unknown"; return Nothing
    Just (SMT.Invalid model) -> case parseAssertion model of
                                  Left err  -> throwError $ "Error parsing "
                                               ++ show model
                                               ++ ":\n"
                                               ++ show err
                                  Right cex -> return $ Just cex

envFreshen :: FreshableNames a => a -> Ceili a
envFreshen a = do
  Env logd loge logi nextIds smtTimeout <- get
  let (nextIds', a') = runFreshen nextIds a
  put $ Env logd loge logi nextIds' smtTimeout
  return a'
