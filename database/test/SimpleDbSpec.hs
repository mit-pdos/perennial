{-# LANGUAGE OverloadedStrings #-}
module SimpleDbSpec(spec) where


import           Prelude hiding (read)

import           Test.Hspec hiding (shouldReturn)
import           Control.Monad.IO.Class

import qualified Coq.BaseLayer as BaseLayer
import           Coq.Common (Key, Value)
import           Coq.Proc (Coq_proc(..))
import qualified Coq.SimpleDb as Db
import           Filesys.Memory (MemFilesysM)
import qualified Filesys.Memory as Mem
import           Interpreter

run :: Coq_proc (BaseLayer.Op x) a -> MemFilesysM a
run = interpret

withFs :: MemFilesysM a -> IO a
withFs = Mem.run

type DbT = Db.Db__Coq_t

newDb :: MemFilesysM DbT
newDb = run Db.newDb

recover :: MemFilesysM DbT
recover = run Db.recover

closeDb :: DbT -> MemFilesysM ()
closeDb db = run $ Db.closeDb db

shutdownDb :: DbT -> MemFilesysM ()
shutdownDb db = run $ Db.shutdownDb db

compact :: DbT -> MemFilesysM ()
compact db = run $ Db.compact db

read :: DbT -> Key -> MemFilesysM (Maybe Value)
read db k = run $ Db.read db k

write :: DbT -> Key -> Value -> MemFilesysM ()
write db k v = run $ Db.write db k v

shouldReturn :: (Show a, Eq a) => MemFilesysM a -> a -> MemFilesysM ()
shouldReturn act expected = do
  x <- act
  liftIO $ x `shouldBe` expected

{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

spec :: Spec
spec = do
  describe "database open, close, recovery" $ do
    it "should initialize" $ withFs $ do
      _ <- newDb
      return ()
    describe "should initialize and shutdown" $ do
      it "should work" $ withFs $ do
        newDb >>= closeDb
      it "should close" $ withFs $ do
        newDb >>= shutdownDb
      it "should close all files" $ Mem.runCheckFds $ do
        newDb >>= closeDb
      it "should recover safely" $ Mem.runCheckFds $ do
        newDb >>= shutdownDb
        recover >>= closeDb
    describe "compaction" $ do
      it "should work work twice" $ withFs $ do
        db <- newDb
        compact db
        closeDb db
  describe "basic database operations" $ do
    it "should read and write" $ withFs $ do
      db <- newDb
      read db 3 `shouldReturn` Nothing
      write db 3 "value"
      read db 3 `shouldReturn` Just "value"
    it "should read after compaction" $ withFs $ do
      db <- newDb
      write db 3 "value"
      compact db
      read db 3 `shouldReturn` Just "value"
    it "should prefer in-memory value" $ withFs $ do
      db <- newDb
      write db 3 "value"
      compact db
      write db 3 "new value"
      read db 3 `shouldReturn` Just "new value"
