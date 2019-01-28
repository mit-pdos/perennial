{-# LANGUAGE OverloadedStrings #-}
module SimpleDbSpec(spec) where


import           Prelude hiding (read)

import           Test.Hspec hiding (shouldReturn)
import           Control.Monad.IO.Class

import           Coq.Common (Key, Value)
import qualified Coq.SimpleDb as Db
import           Filesys.Memory (MemFilesysM)
import qualified Filesys.Memory as Mem
import           Interpreter

{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

withFs :: MemFilesysM a -> IO a
withFs = Mem.run

withFsChecked :: MemFilesysM a -> IO a
withFsChecked act = Mem.run $ act <* Mem.checkFds

type DbT = Db.Db__Coq_t

newDb :: MemFilesysM DbT
newDb = interpret Db.newDb

recover :: MemFilesysM DbT
recover = interpret Db.recover

closeDb :: DbT -> MemFilesysM ()
closeDb db = interpret $ Db.closeDb db

shutdownDb :: DbT -> MemFilesysM ()
shutdownDb db = interpret $ Db.shutdownDb db

compact :: DbT -> MemFilesysM ()
compact db = interpret $ Db.compact db

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

tblClose :: TableW -> MemFilesysM TableT
tblClose t = interpret $ Db.tblWClose t

tblRead :: TableT -> Key -> MemFilesysM (Maybe Value)
tblRead t k = interpret $ Db.tblRead t k

withDb :: (DbT -> MemFilesysM ()) -> IO ()
withDb act = withFs $ do
  db <- newDb
  act db
  closeDb db

shouldReturn :: (Show a, Eq a) => MemFilesysM a -> a -> MemFilesysM ()
shouldReturn act expected = do
  x <- act
  liftIO $ x `shouldBe` expected

beforeCrash :: (DbT -> MemFilesysM ()) -> MemFilesysM ()
beforeCrash act = do
  db <- newDb
  act db
  shutdownDb db

recovered :: (DbT -> MemFilesysM ()) -> MemFilesysM ()
recovered act = do
  db <- recover
  act db
  closeDb db

lifecycleSpec :: Spec
lifecycleSpec = do
  it "should initialize" $ withFs $ do
    _ <- newDb
    return ()
  describe "should initialize and shutdown" $ do
    it "should work" $ withDb $ \_db -> return ()
    it "should close" $ withFs $ do
      newDb >>= shutdownDb
    it "should close all files" $ withFsChecked $ do
      newDb >>= closeDb
    it "should recover safely" $ withFsChecked $ do
      newDb >>= shutdownDb
      recover >>= closeDb
  describe "compaction" $ do
    it "should work" $ withDb compact

basicDatabaseSpec :: Spec
basicDatabaseSpec = do
  it "should read and write" $ withDb $ \db -> do
    read db 3 `shouldReturn` Nothing
    write db 3 "value"
    read db 3 `shouldReturn` Just "value"
  it "should read multiple times" $ withDb $ \db -> do
    write db 1 "v"
    read db 1 `shouldReturn` Just "v"
    read db 1 `shouldReturn` Just "v"
    write db 2 "v2"
    read db 1 `shouldReturn` Just "v"
    read db 2 `shouldReturn` Just "v2"
  it "should compact a write" $ withDb $ \db -> do
    write db 1 "value"
    compact db
  it "should read after compaction" $ withDb $ \db -> do
    write db 3 "value"
    compact db
    read db 3 `shouldReturn` Just "value"
  it "should read after double compaction" $ withDb $ \db -> do
    write db 3 "value"
    compact db
    compact db
    read db 3 `shouldReturn` Just "value"
  it "should prefer in-memory value" $ withDb $ \db -> do
    write db 3 "old value"
    compact db
    write db 3 "new value"
    read db 3 `shouldReturn` Just "new value"

persistenceSpec :: Spec
persistenceSpec = do
  it "should recover persisted writes" $ withFs $ do
    beforeCrash $ \db -> do
      write db 1 "v1"
      compact db
    recovered $ \db -> do
      read db 1 `shouldReturn` Just "v1"
      read db 3 `shouldReturn` Nothing
  it "should not recover buffered writes" $ withFs $ do
    beforeCrash $ \db -> do
      write db 1 "v1"
      compact db
      write db 2 "v2"
    recovered $ \db -> do
      read db 1 `shouldReturn` Just "v1"
      read db 2 `shouldReturn` Nothing
  xit "should recover multiple writes" $ withFs $ do
    beforeCrash $ \db -> do
      write db 1 "value1"
      write db 2 "v2"
      write db 3 "another value"
      compact db
      read db 1 `shouldReturn` Just "value1"
      Mem.printDebugListing
    recovered $ \db -> do
      Mem.printDebugListing
      read db 1 `shouldReturn` Just "value1"
      read db 2 `shouldReturn` Just "v2"
      read db 3 `shouldReturn` Just "another value"
      read db 0 `shouldReturn` Nothing

withTbl :: (TableW -> MemFilesysM ()) -> MemFilesysM TableT
withTbl act = do
  w <- newTbl "table"
  act w
  tblClose w

tableSpec :: Spec
tableSpec = do
  it "should work with a single value" $ withFs $ do
    t <- withTbl $ \w -> do
      tblPut w 1 "v1"
    tblRead t 1 `shouldReturn` Just "v1"
  it "should work with multiple values" $ withFs $ do
    t <- withTbl $ \w -> do
      tblPut w 1 "v1"
      tblPut w 2 "other value"
    tblRead t 1 `shouldReturn` Just "v1"
    tblRead t 2 `shouldReturn` Just "other value"

spec :: Spec
spec = do
  describe "database open, close, recovery" lifecycleSpec
  describe "basic database operations" basicDatabaseSpec
  describe "database should persist correctly" persistenceSpec
  xdescribe "table creation and reading" tableSpec
