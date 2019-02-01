module SimpleDbTesting
  ( withFs
  , DbT
  , withDb
  , new, recover
  , close, crash, persistCrash
  , read, write, compact
  , withTbl
  , newTbl, tblPut, tblWClose
  , tblRead, closeTbl, recoverTbl
  , bracket
  , shouldReturn
  ) where


import           Control.Monad.IO.Class
import           Prelude hiding (read)

import           Test.Hspec (shouldBe)

import           Coq.Common (Key, Value)
import qualified Coq.SimpleDb as Db
import           Filesys.Memory (MemFilesysM)
import qualified Filesys.Memory as Mem
import           Interpreter

{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

withFs :: MemFilesysM a -> IO a
withFs = Mem.run

bracket ::
  MemFilesysM res -- ^ initialize resource
  -> (res -> MemFilesysM ()) -- ^ cleanup resource
  -> (res -> MemFilesysM a) -- ^ action
  -> MemFilesysM a
bracket open close act = do
  res <- open
  x <- act res
  close res
  return x

withDb :: (DbT -> MemFilesysM ()) -> IO ()
withDb = withFs . bracket new close

type DbT = Db.Db__Coq_t

new :: MemFilesysM DbT
new = interpret Db.newDb

recover :: MemFilesysM DbT
recover = interpret Db.recover

close :: DbT -> MemFilesysM ()
close db = interpret (Db.closeDb db) >> Mem.checkFds

crash :: DbT -> MemFilesysM ()
crash db = interpret (Db.shutdownDb db) >> Mem.checkFds

compact :: DbT -> MemFilesysM ()
compact db = interpret $ Db.compact db

persistCrash :: DbT -> MemFilesysM ()
persistCrash db = compact db >> crash db

read :: DbT -> Key -> MemFilesysM (Maybe Value)
read db k = interpret $ Db.read db k

write :: DbT -> Key -> Value -> MemFilesysM ()
write db k v = interpret $ Db.write db k v

type TableW = Db.TblW__Coq_t
type TableT = Db.Tbl__Coq_t

newTbl :: FilePath -> MemFilesysM TableW
newTbl p = interpret $ Db.newTblW p

tblPut :: TableW -> Key -> Value -> MemFilesysM ()
tblPut t k v = interpret $ Db.tblPut t k v

tblWClose :: TableW -> MemFilesysM TableT
tblWClose t = interpret $ Db.tblWClose t

tblRead :: TableT -> Key -> MemFilesysM (Maybe Value)
tblRead t k = interpret $ Db.tblRead t k

closeTbl :: TableT -> MemFilesysM ()
closeTbl t = interpret $ Db.closeTbl t

recoverTbl :: FilePath -> MemFilesysM TableT
recoverTbl p = interpret $ Db.recoverTbl p

withTbl :: (TableW -> MemFilesysM ()) -> MemFilesysM TableT
withTbl act = do
  w <- newTbl "table"
  act w
  tblWClose w

shouldReturn :: (Show a, Eq a) => MemFilesysM a -> a -> MemFilesysM ()
shouldReturn act expected = do
  x <- act
  liftIO $ x `shouldBe` expected
