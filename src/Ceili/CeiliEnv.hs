module Ceili.CeiliEnv
  ( Env(..)
  , Ceili
  , LogLevel(..)
  , checkValid
  , checkValidWithLog
  , defaultEnv
  , envFreshen
  , findCounterexample
  , log_d
  , log_e
  , log_i
  , mkEnv
  , runCeili
  , throwError
  ) where

import Ceili.Assertion ( Assertion(..), parseAssertion )
import Ceili.Name ( CollectableNames, FreshableNames, NextFreshIds, buildFreshIds, runFreshen )
import qualified Ceili.SMT as SMT
import Control.Concurrent.Timeout ( timeout )
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Except ( ExceptT, runExceptT, throwError )
import Control.Monad.Trans.State ( StateT, evalStateT, get, put )
import System.Log.FastLogger

data Env = Env { env_logger_debug :: LogType
               , env_logger_error :: LogType
               , env_logger_info  :: LogType
               , env_nextFreshIds :: NextFreshIds
               , env_smtTimeoutMs :: Integer }

data LogLevel = LogLevelNone
              | LogLevelDebug
              | LogLevelError
              | LogLevelInfo

mkEnv :: CollectableNames n => n -> Env
mkEnv names = Env { env_logger_debug = LogNone -- LogStdout defaultBufSize
                  , env_logger_error = LogStderr defaultBufSize
                  , env_logger_info  = LogStdout defaultBufSize
                  , env_nextFreshIds = buildFreshIds [names]
                  , env_smtTimeoutMs = 2000 }

defaultEnv :: Env
defaultEnv = mkEnv ([] :: [Assertion])

type Ceili a = StateT Env (ExceptT String IO) a

runCeili :: Env -> Ceili a -> IO (Either String a)
runCeili env task = runExceptT (evalStateT task env)

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

checkValid :: Assertion -> Ceili Bool
checkValid = checkValidWithLog LogLevelDebug

checkValidWithLog :: LogLevel -> Assertion -> Ceili Bool
checkValidWithLog level assertion = do
  logType <- logTypeAt level
  result  <- withTimeout $
             withFastLogger logType $ \logger ->
             SMT.checkValidFL logger assertion
  case result of
    Nothing               -> do log_e "SMT timeout"; return False
    Just SMT.Valid        -> return True
    Just (SMT.Invalid _)  -> return False
    Just SMT.ValidUnknown -> do log_e "SMT unknown"; return False

findCounterexample :: Assertion -> Ceili (Maybe Assertion)
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
