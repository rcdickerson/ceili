module Ceili.CeiliEnv
  ( Env(..)
  , Ceili
  , LogLevel(..)
  , checkValid
  , checkValidWithLog
  , defaultEnv
  , log_d
  , log_e
  , log_i
  , runCeili
  , throwError
  ) where

import Ceili.Assertion ( Assertion(..) )
import qualified Ceili.SMT as SMT
import Control.Concurrent.Timeout ( timeout )
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Except ( ExceptT, runExceptT, throwError )
import Control.Monad.Trans.State ( StateT, evalStateT, get )
import System.Log.FastLogger

data Env = Env { logger_debug :: LogType
               , logger_error :: LogType
               , logger_info  :: LogType
               , smtTimeoutMs :: Integer }

data LogLevel = LogLevelNone
              | LogLevelDebug
              | LogLevelError
              | LogLevelInfo

defaultEnv :: Env
defaultEnv = Env { logger_debug = LogNone
                 , logger_error = LogStderr defaultBufSize
                 , logger_info  = LogStdout defaultBufSize
                 , smtTimeoutMs = 2000 }

type Ceili a = StateT Env (ExceptT String IO) a

runCeili :: Env -> Ceili a -> IO (Either String a)
runCeili env task = runExceptT (evalStateT task env)

logAt :: ToLogStr m => (Env -> LogType) -> m -> Ceili ()
logAt logger message = do
  let messageLS = (toLogStr message) <> toLogStr "\n"
  logType <- get >>= return . logger
  liftIO $ withFastLogger logType ($ messageLS)

log_d :: ToLogStr m => m -> Ceili ()
log_d = logAt logger_debug

log_i :: ToLogStr m => m -> Ceili ()
log_i = logAt logger_info

log_e :: ToLogStr m => m -> Ceili ()
log_e = logAt logger_error

logTypeAt :: LogLevel -> Ceili LogType
logTypeAt level = case level of
  LogLevelNone  -> return LogNone
  LogLevelDebug -> get >>= return . logger_debug
  LogLevelError -> get >>= return . logger_error
  LogLevelInfo  -> get >>= return . logger_info

withTimeout :: IO a -> Ceili (Maybe a)
withTimeout t = do
  timeoutMs <- get >>= return . smtTimeoutMs
  liftIO $ timeout (1000 * timeoutMs) t

checkValid :: Assertion -> Ceili Bool
checkValid = checkValidWithLog LogLevelDebug

checkValidWithLog :: LogLevel -> Assertion -> Ceili Bool
checkValidWithLog level assertion = do
  logType <- logTypeAt level
  result  <- withTimeout
           $ withFastLogger logType
           $ \logger -> SMT.checkValidFL logger assertion
  case result of
    Nothing                -> do log_e "SMT timeout"; return False
    Just SMT.Valid         -> return True
    Just (SMT.Invalid msg) -> do log_d msg; return False
    Just SMT.ValidUnknown  -> do log_e "SMT unknown"; return False
