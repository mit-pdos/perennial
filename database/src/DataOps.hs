{-# LANGUAGE TypeApplications #-}
module DataOps where

import           Control.Concurrent.MVar (newMVar, takeMVar, putMVar)
import           Data.IORef (newIORef, readIORef, writeIORef)

import qualified Data.HashTable.IO as H
import qualified Data.Vector.Mutable.Dynamic as V

import           DataStructures
import           Lib (Word64, coerceRet, coerceVoid)

interpret :: Data__Op x -> IO x
interpret (Data__GetVar) = error "there are no variables"
interpret (Data__SetVar _) = error "there are no variables"
interpret (Data__NewIORef x) = coerceRet @(IORef _) $ newIORef x
interpret (Data__ReadIORef r) = readIORef r
interpret (Data__WriteIORef _ Begin) = coerceVoid $ return ()
interpret (Data__WriteIORef r (FinishArgs x)) =
  coerceVoid $ writeIORef r x
interpret Data__NewArray = coerceRet @(Array _) $ V.new 0
interpret (Data__ArrayLength r) =
  coerceRet @Word64 $ fromIntegral <$> V.length r
interpret (Data__ArrayGet r i) = V.unsafeRead r (fromIntegral i)
interpret (Data__ArrayAppend r x) = coerceVoid $ V.pushBack r x
interpret Data__NewHashTable = coerceRet @(HashTable _) H.new
interpret (Data__HashTableAlter h k f) =
  coerceVoid $ H.mutate h k (\v -> (f v, ()))
interpret (Data__HashTableLookup h k) =
  coerceRet $ H.lookup h k
interpret Data__NewLock =
  coerceRet @LockRef $ newMVar ()
interpret (Data__LockAcquire r) =
  coerceVoid $ takeMVar r
interpret (Data__LockRelease r) =
  coerceVoid $ putMVar r ()
