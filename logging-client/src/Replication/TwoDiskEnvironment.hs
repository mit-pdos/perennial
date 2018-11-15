module Replication.TwoDiskEnvironment
  (
    Proc
  , Env
  , disk0
  , disk1
  , requests
  , responses
  , newEnv
  , runTD
  , (>>=)
  , return
  ) where

import Control.Concurrent.MVar (MVar, newEmptyMVar)
import Control.Monad.Reader (ReaderT, runReaderT)
import NbdAPI
import System.Directory (doesFileExist)
import System.IO.Error
import System.Posix.IO
import System.Posix.Types

type CachedHandle = (FilePath, Maybe Fd)

data Env =
  Env { disk0Handle :: CachedHandle
      , disk1Handle :: CachedHandle
      , requests :: MVar Request
      , responses :: MVar Response }

type Proc = ReaderT Env IO

getFd :: CachedHandle -> IO (Maybe Fd)
getFd (_, Nothing) = return Nothing
getFd (fn, Just fd) = do
  exists <- doesFileExist fn
  if exists
    then return (Just fd)
    else return Nothing

disk0 :: Env -> IO (Maybe Fd)
disk0 = getFd . disk0Handle

disk1 :: Env -> IO (Maybe Fd)
disk1 = getFd . disk1Handle

newEnv :: FilePath -> FilePath -> IO Env
newEnv fn0 fn1 = pure Env
  <*> openFile fn0
  <*> openFile fn1
  <*> newEmptyMVar <*> newEmptyMVar
  where openFile :: FilePath -> IO CachedHandle
        openFile path =
          catchIOError (do
              fd <- openFd path ReadWrite Nothing defaultFileFlags
              return (path, Just fd))
          (\e -> if isDoesNotExistError e
                 then return (path, Nothing)
                 else ioError e)


runTD :: Env -> Proc a -> IO a
runTD e m = runReaderT m e
