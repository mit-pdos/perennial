{-# LANGUAGE ExplicitForAll #-}

module Lib
  ( Word64
  , Word8
  , ByteString
  , BS.append
  , Fd
  , IORef
  , Array
  , HashTable
  , LockRef
  , add
  , sub
  , byteString_to_String
  , string_to_ByteString
  , bs_append
  , bs_concat
  , bs_take
  , bs_drop
  , bs_empty
  , bs_length
  , Lib.compare
  , uint64_to_le
  , uint64_from_le
  , coerceRet
  , coerceVoid
  )
where

import           Data.Word (Word64, Word8)
import           System.Posix.Types (Fd)
import           Data.IORef (IORef)

import           Control.Concurrent.ReadWriteLock (RWLock)
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC8
import qualified Data.ByteString.Lazy as BSL
import           Data.HashTable.IO (BasicHashTable)
import           Data.Vector.Mutable.Dynamic (IOVector)
import Data.Binary.Get (getWord64le, runGetOrFail)
import Data.Binary.Put (putWord64le, runPut)

import           Unsafe.Coerce (unsafeCoerce)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

type Array a = IOVector a
type HashTable k v = BasicHashTable k v
type LockRef = RWLock

add :: Word64 -> Word64 -> Word64
add x y = if x > maxBound - y then error "integer overflow" else x+y

sub :: Word64 -> Word64 -> Word64
sub x y = if y >= x then 0 else x - y

compare :: Word64 -> Word64 -> Ordering
compare = Prelude.compare

byteString_to_String :: ByteString -> String
byteString_to_String = BSC8.unpack

string_to_ByteString :: String -> ByteString
string_to_ByteString = BSC8.pack

uint64_to_le :: Word64 -> ByteString
uint64_to_le = BSL.toStrict . runPut . putWord64le

uint64_from_le :: ByteString -> Maybe Word64
uint64_from_le bs =
  case runGetOrFail getWord64le $ BSL.fromStrict bs of
    Left _ -> Nothing
    Right (_, _, x) -> Just x

bs_append :: ByteString -> ByteString -> ByteString
bs_append = BS.append

bs_concat :: [ByteString] -> ByteString
bs_concat = BS.concat

bs_take :: Word64 -> ByteString -> ByteString
bs_take n = BS.take (fromIntegral n)

bs_drop :: Word64 -> ByteString -> ByteString
bs_drop n = BS.drop (fromIntegral n)

bs_empty :: ByteString
bs_empty = BS.empty

bs_length :: ByteString -> Word64
bs_length = fromIntegral . BS.length

-- Some background: our [Op : Type -> Type] definitions are all GADTs but Coq
-- extracts a type with a single type parameter, losing information on the
-- expected return type for each operation. This requires constructing the
-- appropriate value and coercing it to a free type variable.
--
-- When the types are correct this is perfectly safe (due to the Coq type
-- system), but it's easy to make mistakes when using unsafeCoerce. coerceRet is
-- a trick to get some safety back by explicitly annotating and checking the
-- actual return type.
--
-- The key is to use visible type application syntax (foo @Int, after using
-- TypeApplications), and an explicit forall ensures that the desired type
-- variable is first.
{-# INLINE coerceRet #-}
coerceRet :: forall a x f. Functor f => f a -> f x
coerceRet = unsafeCoerce

{-# INLINE coerceVoid #-}
coerceVoid :: Functor f => f () -> f x
coerceVoid = coerceRet
