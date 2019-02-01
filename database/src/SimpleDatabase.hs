module SimpleDatabase
  ( RootFilesysM
  , DbM
  , bracket
  , open, new
  , close, crash
  , read
  , write
  , compact
  ) where

import           Prelude hiding (read)

import           Control.Concurrent.Forkable
import           Control.Monad.Reader

import           Coq.Common (Key, Value)
import qualified Coq.SimpleDb as SimpleDb
import           Filesys.Rooted (RootFilesysM)
import           Interpreter

type Db = SimpleDb.Db__Coq_t

newtype DbM a = DbM (ReaderT Db RootFilesysM a)
  deriving (Functor, Applicative, Monad, MonadIO, ForkableMonad)

usingDb :: (Db -> RootFilesysM a) -> DbM a
usingDb act = DbM (ask >>= lift . act)

bracket :: RootFilesysM Db -> -- ^ initializer
           DbM () -> -- ^ finalizer
           DbM a ->
           RootFilesysM a
bracket open (DbM close) (DbM act) = do
  db <- open
  x <- runReaderT act db
  runReaderT close db
  return x

open :: RootFilesysM Db
open = interpret SimpleDb.recover

new :: RootFilesysM Db
new = interpret SimpleDb.newDb

close :: DbM ()
close = usingDb $ \db -> interpret $ SimpleDb.closeDb db

crash :: DbM ()
crash = usingDb $ \db -> interpret $ SimpleDb.shutdownDb db

read :: Key -> DbM (Maybe Value)
read k = usingDb $ \db -> interpret $ SimpleDb.read db k

write :: Key -> Value -> DbM ()
write k v = usingDb $ \db -> interpret $ SimpleDb.write db k v

compact :: DbM ()
compact = usingDb $ \db -> interpret $ SimpleDb.compact db
