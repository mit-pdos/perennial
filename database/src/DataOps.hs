module DataOps where

import DataStructures
import Data.IORef (newIORef, readIORef, writeIORef)
import qualified Data.HashTable.IO as H

interpret :: Data__Op x -> IO x
interpret (Data__GetVar _) = error "there are no variables"
interpret (Data__SetVar _ _) = error "there are no variables"
interpret (Data__NewIORef x) = unsafeCoerce <$> newIORef x
interpret (Data__ReadIORef r) = unsafeCoerce <$> readIORef r
interpret (Data__WriteIORef _ Begin) =
  unsafeCoerce <$> return ()
interpret (Data__WriteIORef r (FinishArgs x)) =
  unsafeCoerce <$> writeIORef r x
interpret Data__NewArray = error "TODO: arrays"
interpret (Data__ArrayLength _r) = error "TODO: arrays"
interpret (Data__ArrayGet _r _i) = error "TODO: arrays"
interpret (Data__ArrayAppend _r _x) = error "TODO: arrays"
interpret Data__NewHashTable = unsafeCoerce <$> (H.new :: IO (HashTable Any))
interpret (Data__HashTableAlter h k f) =
  H.mutate h k (\v -> (f v, unsafeCoerce ()))
interpret (Data__HashTableLookup h k) =
  unsafeCoerce <$> H.lookup h k
