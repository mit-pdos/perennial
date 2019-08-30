{-# LANGUAGE PackageImports #-}
-- | Monad with an environment to run two-disk operations
module TwoDiskEnvironment
  ( Env
  , newEnv
  , closeEnv
  , deleteEnv
  , Proc
  , runProc
  , forkProc
  , readMem
  , writeMem
  , casMem
  , readDisk
  , writeDisk
  -- to make testing easier
  , encodeValue
  , decodeValue
  )
where

import           Control.Arrow                  ( (>>>) )
import           Control.Concurrent             ( forkIO )
import           Control.Concurrent.MVar
import           Control.Monad.Reader
import           Data.Binary.Get
import           Data.Binary.Put
import           Data.ByteString                ( ByteString )
import qualified Data.ByteString               as BS
import qualified Data.ByteString.Lazy          as BSL
import           System.Directory               ( doesFileExist )
import           System.Posix.Files
import           System.Posix.IO
import "unix-bytestring" System.Posix.IO.ByteString
                                                ( fdPwrite
                                                , fdPread
                                                )
import           System.Posix.Types

import qualified TwoDiskAPI
import           TwoDiskAPI                     ( TwoDisk__Coq_diskId(..) )

type Value = Int

type CachedHandle = (FilePath, Maybe Fd)

numVars :: Int
numVars = fromIntegral TwoDiskAPI.size

data Env =
  Env { memVars :: [MVar Value]
      , disk0Handle :: CachedHandle
      , disk1Handle :: CachedHandle }

type Proc = ReaderT Env IO

openDisk :: FilePath -> IO CachedHandle
openDisk path = do
  exists <- doesFileExist path
  if exists
    then do
      fd <- openFd path ReadWrite Nothing defaultFileFlags
      return (path, Just fd)
    else return (path, Nothing)

newEnv :: FilePath -> IO Env
newEnv path = do
  vars <- replicateM 1000 (newMVar 0)
  let fn0 = path ++ ".0"
      fn1 = path ++ ".1"
  exists0 <- doesFileExist fn0
  exists1 <- doesFileExist fn1
  when (not exists0 && not exists1) $ forM_ [fn0, fn1] $ \p -> do
    fd <- createFile p 0o700
    setFdSize fd (8 * fromIntegral numVars)
  d0 <- openDisk fn0
  d1 <- openDisk fn1
  return $ Env vars d0 d1

closeEnv :: Env -> IO ()
closeEnv env = forM_ [disk0Handle env, disk1Handle env] $ \disk -> do
  fd <- getFd disk
  mapM_ closeFd fd

deleteEnv :: Env -> IO ()
deleteEnv env = forM_ [disk0Handle env, disk1Handle env] $ \(p, _) -> do
  exists <- doesFileExist p
  when exists (removeLink p)

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
    Just fd -> lift $ Just <$> fdPread fd (fromIntegral len) (fromIntegral off)
    Nothing -> return Nothing

writeDiskRange :: TwoDisk__Coq_diskId -> Int -> ByteString -> Proc ()
writeDiskRange did off bs = do
  mfd <- getDisk did
  case mfd of
    Just fd -> do
      lift $ fdPwrite fd bs (fromIntegral off)
      return ()
    Nothing -> return ()

encodeValue :: Value -> ByteString
encodeValue = putInthost >>> runPut >>> BSL.toStrict

decodeValue :: ByteString -> Maybe Value
decodeValue bs = if BS.length bs /= 8
  then Nothing
  else Just $ (BSL.fromStrict >>> runGet getInthost) bs

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
        Nothing -> error $ "bug in decoding integer " ++ show bs
      Nothing -> return Nothing

writeDisk :: TwoDisk__Coq_diskId -> Int -> Value -> Proc ()
writeDisk did i x = if not (0 <= i && i < numVars)
  then error $ "disk write out-of-bounds at " ++ show i
  else writeDiskRange did (8 * i) (encodeValue x)
