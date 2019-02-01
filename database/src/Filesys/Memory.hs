module Filesys.Memory
  ( MemFilesysM
  , run
  , checkFds
  , printDebugListing
  ) where

import           Control.Arrow (second) -- I apologize
import           Control.Concurrent.MVar (MVar, newMVar, withMVar)
import           Control.Monad (void, unless)
import           Control.Monad.IO.Class
import           Control.Monad.Reader (ReaderT, reader, liftIO, runReaderT, lift)
import           Data.IORef (IORef, newIORef, atomicModifyIORef')
import           GHC.Exts (sortWith)

import           Control.Concurrent.Forkable
import qualified Data.ByteString as BS
import qualified Data.HashTable.IO as H
import           Data.Hashable (Hashable)

import           Filesys.Generic
import           Lib (Fd, ByteString)

{-# ANN module ("HLint: ignore Use fmap" :: String) #-}

type HashTable k v = H.CuckooHashTable k v

data State =
  State { files :: HashTable FilePath ByteString
        , handles :: HashTable Int FilePath
        , nextFd :: IORef Int }

newtype Env = Env { filesys :: MVar State }

newtype MemFilesysM a = MemFilesysM (ReaderT Env IO a)
  deriving (Functor, Applicative, Monad, MonadIO, ForkableMonad)

newEnv :: IO Env
newEnv = Env <$> do
  s <- pure State <*> H.new <*> H.new <*> newIORef 1
  newMVar s

run :: MemFilesysM a -> IO a
run (MemFilesysM act) = do
  env <- newEnv
  runReaderT act env

using :: Monad m => (r -> a) -> (a -> m b) -> ReaderT r m b
using f act = do
  x <- reader f
  lift (act x)

withFilesys :: ReaderT State IO a -> MemFilesysM a
withFilesys act = MemFilesysM $
  using filesys $ \m -> withMVar m (runReaderT act)

openFds :: MemFilesysM [FilePath]
openFds = withFilesys $
  using handles (\h -> map snd <$> H.toList h)

checkFds :: MemFilesysM ()
checkFds = do
  openfiles <- openFds
  unless (null openfiles) $ error $ "there are still open fds to " ++ show openfiles

printDebugListing :: MemFilesysM ()
printDebugListing = withFilesys $ do
  listing <- do
    h <- reader files
    ents <- liftIO $ sortWith fst <$> H.toList h
    return $ map (second BS.length) ents
  liftIO $ putStr "file sizes: " >> print listing
  fds <- using handles (\h -> sortWith fst <$> H.toList h)
  liftIO $ putStr "open files: " >> print fds

getFd :: ReaderT State IO Int
getFd = do
  ref <- reader nextFd
  liftIO $ atomicModifyIORef' ref (\fd -> (fd+1, fd))

resolveFd :: Fd -> ReaderT State IO FilePath
resolveFd fh = using handles $ \h -> do
  mp <- H.lookup h (fromIntegral fh)
  case mp of
    Just p -> return p
    Nothing -> error $ "attempt to look up non-existent fd: " ++ show fh

resolvePath :: FilePath -> ReaderT State IO ByteString
resolvePath p = using files $ \h -> do
  mbs <- H.lookup h p
  case mbs of
    Just bs -> return bs
    Nothing -> error $ "attempt to look up non-existent path: " ++ p

htModify :: (Eq k, Hashable k) => HashTable k v -> k -> (v -> v) -> IO ()
htModify h k f = void $ H.mutate h k mutator
  where mutator (Just v) = (Just $ f v, ())
        mutator Nothing = (Nothing, ())

instance MonadFilesys MemFilesysM where
  open p = withFilesys $ do
    fd <- getFd
    using handles $ \h -> H.insert h fd p
    return . fromIntegral $ fd
  create p = withFilesys $ do
    fd <- getFd
    using handles $ \h -> H.insert h fd p
    using files $ \h -> H.insert h p BS.empty
    return . fromIntegral $ fd
  close fh = withFilesys $
    using handles $ \h -> H.delete h (fromIntegral fh)
  size fh = withFilesys $ do
    bs <- resolveFd fh >>= resolvePath
    return . fromIntegral . BS.length $ bs
  readAt fh off len = withFilesys $ do
    bs <- resolveFd fh >>= resolvePath
    return $ BS.take (fromIntegral len) (BS.drop (fromIntegral off) bs)
  delete p = withFilesys $
    using files $ \h -> H.delete h p
  rename p1 p2 = withFilesys $
    using files $ \h -> do
      Just bs <- H.lookup h p1
      H.delete h p1
      H.insert h p2 bs
  atomicCreate p bs = withFilesys $
    using files $ \h -> H.insert h p bs
  append fh bs = withFilesys $ do
    p <- resolveFd fh
    using files $ \h -> htModify h p (`BS.append` bs)
  ftruncate p = withFilesys $
    using files $ \h -> H.insert h p BS.empty
  list = withFilesys $
    using files $ \h -> map fst <$> H.toList h
