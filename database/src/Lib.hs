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
  , Lib.compare
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
import           Data.HashTable.IO (BasicHashTable)
import           Data.Vector.Mutable.Dynamic (IOVector)

import           Unsafe.Coerce (unsafeCoerce)

type Array a = IOVector a
type HashTable k v = BasicHashTable k v
type LockRef = RWLock

add :: Word64 -> Word64 -> Word64
add x y = if x > maxBound - y then error "integer overflow" else x+y

sub :: Word64 -> Word64 -> Word64
sub x y = if y >= x then 0 else x - y

compare :: Word64 -> Word64 -> Ordering
compare = Prelude.compare

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
coerceRet :: forall a x f. Functor f => f a -> f x
coerceRet = fmap unsafeCoerce

coerceVoid :: Functor f => f () -> f x
coerceVoid = fmap unsafeCoerce
