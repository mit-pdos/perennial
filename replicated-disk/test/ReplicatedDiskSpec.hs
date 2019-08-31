module ReplicatedDiskSpec where

import           Control.Concurrent.MVar
import           Control.Exception
import           Control.Monad
import           Control.Monad.Trans
import           Prelude                 hiding ( read )
import           System.Posix.Files
import           Test.Hspec

import           ReplicatedDisk
import           TwoDiskEnvironment

{-# ANN module "HLint: ignore Redundant do" #-}

shouldProduce :: (Show a, Eq a) => Proc a -> a -> Proc ()
shouldProduce comp x = do
  actual <- comp
  liftIO $ actual `shouldBe` x

withEnv :: Proc a -> IO a
withEnv act = bracket (newEnv "/tmp/disk")
                      (\env -> closeEnv env >> deleteEnv env)
                      (\env -> runProc env act)

spec :: Spec
spec = do
  describe "replicated disk" $ do
    it "should read and write addresses" $ withEnv $ do
      read 0 `shouldProduce` 0
      write 1 100
      read 0 `shouldProduce` 0
      read 1 `shouldProduce` 100
    it "should support recovery" $ withEnv $ do
      write 1 100
      write 2 200
      recv
      read 1 `shouldProduce` 100
      read 2 `shouldProduce` 200
    it "should support failures" $ withEnv $ do
      write 1 100
      write 2 200
      liftIO $ removeLink "/tmp/disk.0"
      read 1 `shouldProduce` 100
      read 2 `shouldProduce` 200
    it "should support concurrency" $ withEnv $ do
      vars <- forM [0 .. 999] $ \a -> do
        v <- liftIO newEmptyMVar
        forkProc $ do
          write a 0
          write a 1
          write a a
          liftIO $ putMVar v ()
        return v
      liftIO $ forM_ vars takeMVar
      forM_ [0 .. 999] $ \a -> do
        read a `shouldProduce` a
    it "should recover after a disk failure" $ do
      env <- newEnv "/tmp/disk"
      runProc env (write 1 100)
      removeLink "/tmp/disk.0"
      closeEnv env
      env <- newEnv "/tmp/disk"
      runProc env recv
      runProc env (read 1) `shouldReturn` 100
      runProc env (read 2) `shouldReturn` 0
      closeEnv env
      deleteEnv env
