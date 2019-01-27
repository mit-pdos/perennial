{-# LANGUAGE TypeApplications  #-}
module FilesysOps
  ( interpret
  ) where

import Coq.Filesys
import Filesys.Generic
import Lib (Fd, Word64, ByteString,
            coerceRet, coerceVoid)

interpret :: MonadFilesys m => FS__Op x -> m x
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
