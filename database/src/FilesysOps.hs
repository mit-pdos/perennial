{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeApplications  #-}
module FilesysOps
  ( Env(..)
  , FilesysM
  , interpret
  ) where

import                   Control.Monad (when)
import                   Control.Monad.Reader (ReaderT, reader, liftIO)
import qualified         Data.ByteString as BS
import                   System.Directory (listDirectory, removeFile)
import                   System.FilePath.Posix (joinPath)
import                   System.Posix.Files (getFdStatus, fileSize, setFileSize, rename)
import                   System.Posix.IO ( openFd,  OpenMode(..)
                       , closeFd)
import qualified         System.Posix.IO as PosixIO
import "unix-bytestring" System.Posix.IO.ByteString (fdPread, fdWrite)
import                   System.Posix.Types (Fd)

import                   Filesys
import                   Lib (Word64, ByteString, coerceRet, coerceVoid)

newtype Env = Env { filesysRoot :: FilePath }

type FilesysM = ReaderT Env IO

withRoot :: (FilePath -> IO a) -> FilesysM a
withRoot act = do
  root <- reader filesysRoot
  liftIO $ act root

resolvePath :: FilePath -> (FilePath -> IO a) -> FilesysM a
resolvePath f act = withRoot $ \root -> act (joinPath [root, f])

interpret :: FS__Op x -> FilesysM x
interpret (FS__Open p) =
  let perms = Nothing
      mode = PosixIO.defaultFileFlags in
    coerceRet @Fd $ resolvePath p $ \f -> openFd f ReadOnly perms mode
interpret (FS__Create p) =
  let perms = Just 0644
      mode = PosixIO.defaultFileFlags {PosixIO.append=True} in
    coerceRet @Fd $ resolvePath p $ \f -> openFd f ReadWrite perms mode
interpret FS__List =
  coerceRet @[String] $ withRoot $ \root -> listDirectory root
interpret (FS__Size fh) = liftIO $ do
    s <- getFdStatus fh
    coerceRet @Word64 $ return . fromIntegral . fileSize $ s
interpret (FS__Close fh) = liftIO . coerceVoid $ closeFd fh
interpret (FS__Delete p) = coerceVoid $ resolvePath p $ \f -> removeFile f
interpret (FS__Truncate p) = liftIO . coerceVoid $ setFileSize p 0
interpret (FS__Rename p1 p2) = coerceVoid . withRoot $ \root ->
  let src = joinPath [root, p1]
      dst = joinPath [root, p2] in
    rename src dst
interpret (FS__ReadAt f off len) = liftIO . coerceRet @ByteString $ do
  bs <- fdPread f (fromIntegral len) (fromIntegral off)
  when (BS.length bs < fromIntegral len) $ error "short read"
  return bs
interpret (FS__Append f bs) = liftIO . coerceVoid $ do
  count <- fdWrite f bs
  when (fromIntegral count < BS.length bs) $ error "short write"
interpret (FS__AtomicCreate f bs) = coerceVoid . withRoot $ \root -> do
    let dstFile = joinPath [root, f]
    let tmpFile = dstFile ++ ".tmp"
    BS.writeFile tmpFile bs
    rename tmpFile dstFile
