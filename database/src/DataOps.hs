module DataOps where

import Lib (Word64)
import DataStructures
import Data.IORef (newIORef, readIORef, writeIORef)
import qualified Data.HashTable.IO as H
import qualified Data.Vector.Mutable.Dynamic as V

interpret :: Data__Op x -> IO x
interpret (Data__GetVar _) = error "there are no variables"
interpret (Data__SetVar _ _) = error "there are no variables"
interpret (Data__NewIORef x) = unsafeCoerce <$> newIORef x
interpret (Data__ReadIORef r) = unsafeCoerce <$> readIORef r
interpret (Data__WriteIORef _ Begin) =
  unsafeCoerce <$> return ()
interpret (Data__WriteIORef r (FinishArgs x)) =
  unsafeCoerce <$> writeIORef r x
interpret Data__NewArray = unsafeCoerce <$> V.new 0
interpret (Data__ArrayLength r) = do
  l <- V.length r
  return $ unsafeCoerce (fromIntegral l :: Word64)
interpret (Data__ArrayGet r i) = V.unsafeRead r (fromIntegral i)
interpret (Data__ArrayAppend r x) = unsafeCoerce <$> V.pushBack r x
interpret Data__NewHashTable = unsafeCoerce <$> (H.new :: IO (HashTable Any))
interpret (Data__HashTableAlter h k f) =
  H.mutate h k (\v -> (f v, unsafeCoerce ()))
interpret (Data__HashTableLookup h k) =
  unsafeCoerce <$> H.lookup h k
