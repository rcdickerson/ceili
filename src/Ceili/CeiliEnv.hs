module Ceili.CeiliEnv
  ( Env(..)
  , Ceili
  , checkValid
  , defaultEnv
  , log_d
  , log_e
  , log_i
  , runCeili
  ) where

import Ceili.Assertion ( Assertion(..) )
import qualified Ceili.SMT as SMT
import Control.Concurrent.Timeout ( timeout )
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Except ( ExceptT, runExceptT )
import Control.Monad.Trans.State ( StateT, evalStateT, get )
import System.IO ( hFlush, hPutStrLn, stderr, stdout )

data Env = Env { smtTimeoutMs :: Integer }

defaultEnv :: Env
defaultEnv = Env { smtTimeoutMs = 2000 }

type Ceili a = StateT Env (ExceptT String IO) a

runCeili :: Env -> Ceili a -> IO (Either String a)
runCeili env task = runExceptT (evalStateT task env)

log_d :: String -> Ceili ()
log_d message = liftIO $ do
  putStrLn message
  hFlush stdout

log_i :: String -> Ceili ()
log_i message = liftIO $ do
  putStrLn message
  hFlush stdout

log_e :: String -> Ceili ()
log_e message = liftIO $ do
  hPutStrLn stderr message
  hFlush stderr

withTimeout :: IO a -> Ceili (Maybe a)
withTimeout t = do
  timeoutMs <- get >>= return . smtTimeoutMs
  liftIO $ timeout (1000 * timeoutMs) t

checkValid :: Assertion -> Ceili Bool
checkValid assertion = do
  result <- withTimeout $ SMT.checkValid assertion
  case result of
    Nothing               -> do log_e "SMT timeout"; return False
    Just SMT.Valid        -> return True
    Just (SMT.Invalid _)  -> return False
    Just SMT.ValidUnknown -> do log_e "SMT unknown"; return False
