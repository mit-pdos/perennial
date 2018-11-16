{-# LANGUAGE PackageImports #-}
module Replication.TwoDiskOps where

import                   Control.Monad (void, when, forM_)
import                   Control.Monad.Reader (reader, liftIO)
import qualified         Data.ByteString as BS
import                   Disk
import                   Proc
import                   Replication.TwoDiskEnvironment
import                   System.Directory (doesFileExist)
import                   System.IO (SeekMode(..),
                                    IOMode(WriteMode),
                                    withFile,
                                    hSetFileSize)
import "unix-bytestring" System.Posix.IO.ByteString
import                   System.Posix.Types (Fd)
import                   TwoDiskAPI
import                   Utils.Conversion

type DiskResult = TwoDisk__DiskResult
type DiskId = TwoDisk__Coq_diskId

getDisk :: DiskId -> Proc (Maybe Fd)
getDisk TwoDisk__Coq_d0 = reader disk0 >>= liftIO
getDisk TwoDisk__Coq_d1 = reader disk1 >>= liftIO

ifExists :: DiskId -> (Fd -> IO a) -> Proc (DiskResult a)
ifExists d m = do
  mfd <- getDisk d
  liftIO $ case mfd of
      Just fd -> TwoDisk__Working <$> m fd
      Nothing -> return TwoDisk__Failed

getSizeBlocks :: Fd -> IO Integer
getSizeBlocks fd = do
    off <- fdSeek fd SeekFromEnd 0
    return (fromIntegral off `div` blocksize)

-- need to prefix to avoid conflict with Prelude.read
td_read :: DiskId -> Coq_addr -> Proc (DiskResult BS.ByteString)
td_read d a = ifExists d $ \fd -> do
  sz <- getSizeBlocks fd
  if a < sz then
    fdPread fd blocksize (fromIntegral $ addrToOffset a)
  else
    return (BS.replicate blocksize 0)

write :: DiskId -> Coq_addr -> BS.ByteString -> Proc (DiskResult ())
write d a b = ifExists d $ \fd -> do
  sz <- getSizeBlocks fd
  when (a < sz) (void $ fdPwrite fd b (fromIntegral $ addrToOffset a))

-- |implementation of two disk DiskSize operation - note that this size is
-- reported to Coq in blocks
size :: DiskId -> Proc (DiskResult Integer)
size d = ifExists d getSizeBlocks

interpretOp :: TwoDisk__Op a -> Proc a
interpretOp (TwoDisk__Coq_op_read d a) = unsafeCoerce <$> td_read d a
interpretOp (TwoDisk__Coq_op_write d a b) = unsafeCoerce <$> write d a b
interpretOp (TwoDisk__Coq_op_size d) = unsafeCoerce <$> size d

interpret :: Coq_proc (TwoDisk__Op x) a -> Proc a
interpret (Call op) = unsafeCoerce <$> interpretOp op
interpret (Ret v) = return v
interpret (Bind p1 p2) = interpret p1 >>= interpret . p2

init :: FilePath -> FilePath -> Integer -> IO Env
init fn0 fn1 sizeBytes = do
  exists0 <- doesFileExist fn0
  exists1 <- doesFileExist fn1
  when (not exists0 && not exists1) $
    forM_ [fn0, fn1] $ \p ->
      withFile p WriteMode $ \h ->
        hSetFileSize h sizeBytes
  newEnv fn0 fn1
