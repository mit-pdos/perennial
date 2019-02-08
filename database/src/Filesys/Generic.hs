module Filesys.Generic where

import Lib (Word64, Fd, ByteString)

-- A MonadFilesys exposes the filesystem APIs in the Filesys layer, in some
-- ambient monad
class Monad m => MonadFilesys m where
  open :: FilePath -> m Fd
  close :: Fd -> m ()

  -- reading
  list :: m [FilePath]
  size :: Fd -> m Word64
  -- readAt fh offset length
  readAt :: Fd -> Word64 -> Word64 -> m ByteString

  -- modifying
  create :: FilePath -> m Fd
  append :: Fd -> ByteString -> m ()
  delete :: FilePath -> m ()
  ftruncate :: FilePath -> m ()
  rename :: FilePath -> FilePath -> m ()
  atomicCreate :: FilePath -> ByteString -> m ()
  link :: FilePath -> FilePath -> m Bool
