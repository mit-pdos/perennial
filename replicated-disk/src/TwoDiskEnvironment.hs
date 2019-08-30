{-# LANGUAGE PackageImports #-}
-- | Monad with an environment to run two-disk operations
module TwoDiskEnvironment
  ( Env
  , newEnv
  , Proc
  , runProc
  , forkProc
  , readMem
  , writeMem
  , casMem
  , readDisk
  , writeDisk
  )
where

import           System.Directory               ( doesFileExist )
import           Control.Concurrent             ( forkIO )
import           Control.Concurrent.MVar
import           System.Posix.Types
import           Control.Monad.Reader
import qualified Data.ByteString               as BS
import           Data.ByteString                ( ByteString )
import qualified TwoDiskAPI
import           TwoDiskAPI                     ( TwoDisk__Coq_diskId(..) )
import           Control.Arrow                  ( (>>>) )
import "unix-bytestring" System.Posix.IO.ByteString
                                                ( fdPwrite
                                                , fdPread
                                                )
import           System.Posix.IO
import           System.Posix.Files

type Value = Int

type CachedHandle = (FilePath, Maybe Fd)

numVars :: Int
numVars = fromIntegral TwoDiskAPI.size

data Env =
  Env { memVars :: [MVar Value]
      , disk0Handle :: CachedHandle
      , disk1Handle :: CachedHandle }

type Proc = ReaderT Env IO

newDisk :: FilePath -> IO CachedHandle
newDisk path = do
  fd <- openFd path ReadWrite Nothing defaultFileFlags
  setFdSize fd (8 * fromIntegral numVars)
  return (path, Just fd)

newEnv :: FilePath -> IO Env
newEnv path = do
  vars <- replicateM 1000 (newMVar 0)
  d0   <- newDisk (path ++ ".0")
  d1   <- newDisk (path ++ ".1")
  return $ Env vars d0 d1

runProc :: Env -> Proc a -> IO a
runProc env p = runReaderT p env

forkProc :: Proc a -> Proc ()
forkProc p = do
  env <- ask
  lift . forkIO $ void (runReaderT p env)
  return ()

getMem :: Int -> Proc (MVar Value)
getMem i = if not (0 <= i && i < numVars)
  then error $ "out-of-bounds memory access to " ++ show i
  else asks $ memVars >>> (!! i)

getFd :: CachedHandle -> IO (Maybe Fd)
getFd (_ , Nothing) = return Nothing
getFd (fn, Just fd) = do
  exists <- doesFileExist fn
  if exists then return (Just fd) else return Nothing

getDisk :: TwoDisk__Coq_diskId -> Proc (Maybe Fd)
getDisk TwoDisk__Coq_d0 = do
  h <- asks disk0Handle
  lift $ getFd h
getDisk TwoDisk__Coq_d1 = do
  h <- asks disk1Handle
  lift $ getFd h

readDiskRange :: TwoDisk__Coq_diskId -> Int -> Int -> Proc (Maybe ByteString)
readDiskRange did off len = do
  mfd <- getDisk did
  case mfd of
    Just fd -> lift $ Just <$> fdPread fd (fromIntegral off) (fromIntegral len)
    Nothing -> return Nothing

writeDiskRange :: TwoDisk__Coq_diskId -> Int -> ByteString -> Proc ()
writeDiskRange did off bs = do
  mfd <- getDisk did
  case mfd of
    Just fd -> do
      lift $ fdPwrite fd bs (fromIntegral off)
      return ()
    Nothing -> return ()

encodeValue :: Int -> ByteString
encodeValue x = undefined

decodeValue :: ByteString -> Maybe Int
decodeValue bs = Just undefined

-- op implementations

readMem :: Int -> Proc Value
readMem i = do
  v <- getMem i
  lift $ readMVar v

setMVar :: a -> MVar a -> IO ()
setMVar x v = modifyMVar_ v (\_ -> return x)

writeMem :: Int -> Value -> Proc ()
writeMem i x = do
  v <- getMem i
  lift $ setMVar x v

casMem :: Int -> Value -> Value -> Proc Value
casMem i expected vnew = do
  v <- getMem i
  lift $ modifyMVar
    v
    (\old -> return (if old == expected then vnew else old, old))

readDisk :: TwoDisk__Coq_diskId -> Int -> Proc (Maybe Value)
readDisk did i = if not (0 <= i && i < numVars)
  then error $ "disk read out-of-bounds at " ++ show i
  else do
    mbs <- readDiskRange did (8 * i) 8
    case mbs of
      Just bs -> case decodeValue bs of
        Just v  -> return (Just v)
        Nothing -> error "bug in decoding integer"
      Nothing -> return Nothing

writeDisk :: TwoDisk__Coq_diskId -> Int -> Value -> Proc ()
writeDisk did i x = if not (0 <= i && i < numVars)
  then error $ "disk write out-of-bounds at " ++ show i
  else writeDiskRange did (8 * i) (encodeValue x)
