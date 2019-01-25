module Lib
  ( Word64
  , ByteString
  , BS.append
  , Fd
  , IORef
  , Array
  , HashTable
  , add
  , sub
  , Lib.compare
  )
where

import Data.Word (Word64)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import System.Posix.Types (Fd)

-- data structures
import Data.IORef (IORef)
import Data.Vector.Mutable.Dynamic (IOVector)
import Data.HashTable.IO (BasicHashTable)

type Array a = IOVector a
type HashTable k v = BasicHashTable k v

add :: Word64 -> Word64 -> Word64
add x y = if x > maxBound - y then error "integer overflow" else x+y

sub :: Word64 -> Word64 -> Word64
sub x y = if y >= x then 0 else x - y

compare :: Word64 -> Word64 -> Ordering
compare = Prelude.compare
