{-# LANGUAGE TypeApplications  #-}
module FilesysOps
  ( interpret
  ) where

import Control.Monad.IO.Class
import System.Random (randomIO)

import Coq.Filesys
import Filesys.Generic
import Lib (Fd, Word64, ByteString,
            coerceRet, coerceVoid)

interpret :: (MonadFilesys m, MonadIO m) => FS__Op x -> m x
interpret (FS__Open p) = coerceRet @Fd $ open p
interpret (FS__Create p) = coerceRet @Fd $ create p
interpret FS__List = coerceRet @[String] list
interpret (FS__Size fh) = coerceRet @Word64 $ size fh
interpret (FS__Close fh) = coerceVoid $ close fh
interpret (FS__Delete p) = coerceVoid $ delete p
interpret (FS__Truncate p) = coerceVoid $ ftruncate p
interpret (FS__Rename p1 p2) = coerceVoid $ rename p1 p2
interpret (FS__ReadAt fh off len) = coerceRet @ByteString $ readAt fh off len
interpret (FS__Append fh bs) = coerceVoid $ append fh bs
interpret (FS__AtomicCreate f bs) = coerceVoid $ atomicCreate f bs
interpret (FS__Link p1 p2) = coerceRet @Bool $ link p1 p2
interpret FS__GetPID = error "Haskell does not have numeric ThreadIDs"
-- TODO: really shouldn't be in the filesystem layer (at best data structures,
-- better yet a separate state-independent layer)
interpret FS__Random = coerceRet @Word64 $ liftIO randomIO
