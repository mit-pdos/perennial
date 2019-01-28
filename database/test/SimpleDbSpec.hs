module SimpleDbSpec(spec) where

import           Test.Hspec

import qualified Coq.BaseLayer as BaseLayer
import           Coq.Proc (Coq_proc(..))
import qualified           Coq.SimpleDb as Db
import qualified Filesys.Memory as Mem
import           Interpreter

run :: Coq_proc (BaseLayer.Op x) a -> Mem.MemFilesysM a
run = interpret

withFs :: Mem.MemFilesysM a -> IO a
withFs = Mem.run

type DbT = Db.Db__Coq_t

newDb :: Mem.MemFilesysM DbT
newDb = run Db.newDb

recover :: Mem.MemFilesysM DbT
recover = run Db.recover

closeDb :: DbT -> Mem.MemFilesysM ()
closeDb db = run $ Db.closeDb db

{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

spec :: Spec
spec = do
  describe "basic database operations" $ do
    it "should initialize" $ withFs $ do
      _ <- newDb
      return ()
    describe "should initialize and shutdown" $ do
      it "should work" $ withFs $ do
        newDb >>= closeDb
      it "should close all files" $ Mem.runCheckFds $ do
        newDb >>= closeDb
      it "should recover safely" $ Mem.runCheckFds $ do
        newDb >>= closeDb
        recover >>= closeDb
