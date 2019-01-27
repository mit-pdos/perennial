{-# LANGUAGE PackageImports #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Filesys.Rooted
  ( RootFilesysM
  , run
  ) where

import                   Control.Monad (when)
import                   Control.Monad.Reader (ReaderT, MonadReader, reader, liftIO, runReaderT)
import qualified         Data.ByteString as BS
import                   System.Directory (listDirectory, removeFile)
import                   System.FilePath.Posix (joinPath)
import                   System.Posix.Files (getFdStatus,
                                             fileSize,
                                             setFileSize,
                                             rename,
                                             ownerReadMode, ownerWriteMode,
                                             unionFileModes)
import                   System.Posix.IO ( openFd,  OpenMode(..)
                       , closeFd)
import qualified         System.Posix.IO as PosixIO
import "unix-bytestring" System.Posix.IO.ByteString (fdPread, fdWrite)

import                   Filesys.Generic
import                   Control.Monad.IO.Class
import                   Control.Concurrent.Forkable

newtype Env = Env { filesysRoot :: FilePath }

newtype RootFilesysM a = RootFilesysM (ReaderT Env IO a)
  deriving (Functor, Applicative, Monad, MonadIO, ForkableMonad, MonadReader Env)

withRoot :: (FilePath -> IO a) -> RootFilesysM a
withRoot act = do
  root <- reader filesysRoot
  liftIO $ act root

resolvePath :: (FilePath -> IO a) -> FilePath -> RootFilesysM a
resolvePath act f = withRoot $ \root -> act (joinPath [root, f])

run :: FilePath -> RootFilesysM a -> IO a
run root (RootFilesysM act) = runReaderT act (Env root)

instance MonadFilesys RootFilesysM where
  open = let perms = Nothing
             mode = PosixIO.defaultFileFlags in
           resolvePath $ \f -> openFd f ReadOnly perms mode
  create = let perms = Just (ownerReadMode `unionFileModes` ownerWriteMode)
               mode = PosixIO.defaultFileFlags {PosixIO.append=True} in
             resolvePath $ \f -> openFd f ReadWrite perms mode
  list = withRoot $ \root -> listDirectory root
  size f = liftIO $ do
    s <- getFdStatus f
    return $ fromIntegral . fileSize $ s
  close f = liftIO $ closeFd f
  delete = resolvePath $ \f -> removeFile f
  ftruncate = resolvePath $ \f -> setFileSize f 0
  readAt f off len = liftIO $
    fdPread f (fromIntegral len) (fromIntegral off)
  append f bs = liftIO $ do
    count <- fdWrite f bs
    when (fromIntegral count < BS.length bs) $ error "short write"
  rename f1 f2 = withRoot $ \root ->
    System.Posix.Files.rename (joinPath [root, f1]) (joinPath [root, f2])
  atomicCreate f bs = withRoot $ \root -> do
    let dstFile = joinPath [root, f]
    let tmpFile = dstFile ++ ".tmp"
    BS.writeFile tmpFile bs
    System.Posix.Files.rename tmpFile dstFile
