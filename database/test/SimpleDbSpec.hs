module SimpleDbSpec(spec) where

import           Test.Hspec

import qualified Coq.BaseLayer as BaseLayer
import           Coq.Proc (Coq_proc(..))
import           Coq.SimpleDb
import qualified Filesys.Memory as Mem
import           Interpreter

run :: Coq_proc (BaseLayer.Op x) a -> Mem.MemFilesysM a
run = interpret

withFs :: Mem.MemFilesysM a -> IO a
withFs = Mem.run

{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

spec :: Spec
spec = do
  describe "basic database operations" $ do
    it "should initialize" $ withFs $ do
      run $ newDb
      return ()
    describe "should initialize and shutdown" $ do
      it "should work" $ withFs $ do
        db <- run $ newDb
        run $ closeDb db
      it "should close all files" $ Mem.runCheckFds $ do
        db <- run $ newDb
        run $ closeDb db
      it "should recover safely" $ Mem.runCheckFds $ do
        db <- run $ newDb
        run $ closeDb db
        db <- run $ recover
        run $ closeDb db
