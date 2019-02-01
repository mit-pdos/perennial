module SimpleDbSpec(spec) where


import           Prelude hiding (read)

import qualified Data.ByteString.Char8 as BSC8
import qualified Data.List as List
import           Test.Hspec hiding (shouldReturn)

import SimpleDbTesting

{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

nothing :: Monad m => DbT -> m ()
nothing _ = return ()

lifecycleSpec :: Spec
lifecycleSpec = do
  it "should initialize" $ withFs $ bracket new nothing nothing
  describe "should initialize and shutdown" $ do
    it "should work" $ withDb nothing
    it "should close all files" $ withFs $ bracket new close nothing
    it "should recover safely" $ withFs $ do
      bracket new crash nothing
      bracket recover close nothing
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
    bracket new crash $ \db -> do
      write db 1 "v1"
      compact db
    bracket recover close $ \db -> do
      read db 1 `shouldReturn` Just "v1"
      read db 3 `shouldReturn` Nothing
  it "should not recover buffered writes" $ withFs $ do
    bracket new crash $ \db -> do
      write db 1 "v1"
      compact db
      write db 2 "v2"
    bracket recover close $ \db -> do
      read db 1 `shouldReturn` Just "v1"
      read db 2 `shouldReturn` Nothing
  it "should recover multiple writes" $ withFs $ do
    bracket new persistCrash $ \db -> do
      write db 1 "value1"
      write db 2 "v2"
      write db 3 "another value"
    bracket recover crash $ \db -> do
      read db 1 `shouldReturn` Just "value1"
      read db 2 `shouldReturn` Just "v2"
      read db 3 `shouldReturn` Just "another value"
      read db 0 `shouldReturn` Nothing
  it "should persist multiple tables" $ withFs $ do
    bracket new persistCrash $ \db -> do
      write db 1 "v1"
      write db 2 "v2"
    bracket recover persistCrash $ \db -> do
      write db 3 "v3"
      write db 4 "v4"
    bracket recover close $ \db -> do
      read db 1 `shouldReturn` Just "v1"
      read db 3 `shouldReturn` Just "v3"
  it "should overwrite table values" $ withFs $ do
    bracket new close $ \db -> do
      write db 1 "v1"
    bracket recover persistCrash $ \db -> do
      write db 1 "v2"
    bracket recover close $ \db -> do
      read db 1 `shouldReturn` Just "v2"
      write db 1 "v3"
      read db 1 `shouldReturn` Just "v3"

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
  it "should work with large values" $ withFs $ do
    let largeVal n = BSC8.pack (List.replicate n 'a')
    t <- withTbl $ \w -> do
      tblPut w 3 "small"
      tblPut w 1 (largeVal 5000)
      tblPut w 2 "also small"
    tblRead t 1 `shouldReturn` Just (largeVal 5000)
    tblRead t 3 `shouldReturn` Just "small"
    tblRead t 2 `shouldReturn` Just "also small"
  it "should recover correctly" $ withFs $ do
    t <- withTbl $ \w -> do
      tblPut w 1 "v1"
      tblPut w 3 "v3"
    closeTbl t
    t <- recoverTbl "table"
    tblRead t 1 `shouldReturn` Just "v1"
    tblRead t 3 `shouldReturn` Just "v3"

spec :: Spec
spec = do
  describe "database open, close, recovery" lifecycleSpec
  describe "basic database operations" basicDatabaseSpec
  describe "table creation and reading" tableSpec
  describe "database should persist correctly" persistenceSpec
