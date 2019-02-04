module SimpleDbConcurrentSpec(spec) where

import Control.Concurrent.MVar (MVar, newEmptyMVar, putMVar, takeMVar)
import Control.Monad (forM, forM_, replicateM_,
                      when)
import Prelude hiding (read, reads)

import Control.Concurrent.Forkable
import Control.Monad.Catch (MonadMask, finally)
import Control.Monad.IO.Class
import Test.Hspec hiding (shouldReturn)

import Filesys.Memory (MemFilesysM)
import Lib (ByteString)
import SimpleDbTesting

{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

type DoneChannel = MVar ()

newChannel :: MonadIO m => m DoneChannel
newChannel = liftIO newEmptyMVar

sendDone :: MonadIO m => DoneChannel -> m ()
sendDone c = liftIO $ putMVar c ()

spawn :: (ForkableMonad m, MonadIO m, MonadMask m) => m a -> m DoneChannel
spawn act = do
  c <- newChannel
  _ <- forkIO $ finally act (sendDone c)
  return c

waitFor :: MonadIO m => DoneChannel -> m ()
waitFor = liftIO . takeMVar

runAll_ :: (ForkableMonad m, MonadIO m, MonadMask m) => [m ()] -> m ()
runAll_ acts = do
  mvars <- forM acts spawn
  mapM_ waitFor mvars

writes :: DbT -> MemFilesysM ()
writes db = forM_ [1..1000] $ \k -> write db k "val"

reads :: DbT -> [Maybe ByteString] -> MemFilesysM ()
reads db allowed = forM_ [1..1000] $ \k -> do
  v <- read db k
  liftIO $ v `shouldSatisfy` (`elem` allowed)

compactions :: DbT -> MemFilesysM ()
compactions = replicateM_ 100 . compact

readsVal :: DbT -> MemFilesysM ()
readsVal db = reads db [Just "val"]

spec :: Spec
spec = do
  describe "concurrent operations should not crash" $ do
    it "should handle concurrent reads" $ withDb $ \db -> do
      writes db
      compact db
      runAll_ $ replicate 10 $ readsVal db
    it "should handle concurrent writes" $ withDb $ \db -> do
      runAll_ $ replicate 10 $ writes db
    it "should handle mixed reads, writes" $ withDb $ \db -> do
      runAll_ $ concat $ replicate 10 [reads db [Nothing, Just "val"], writes db]
    it "should handle reads, writes, and compactions" $ withDb $ \db -> do
      runAll_ $ [reads db [Nothing, Just "val"], compactions db] ++ replicate 10 (writes db)
  describe "readers observe writes" $ do
    it "should ensure readers observe old results" $ withDb $ \db -> do
      let writer = forM_ [1001..2000] $ \k -> write db k "new val"
      writes db
      compact db
      runAll_ $ replicate 10 (readsVal db) ++ replicate 10 writer
    it "should ensure compactions do not impact readers" $ withDb $ \db -> do
      let reader = forM_ [1..100] $ \k -> read db k `shouldReturn` Just "val"
      writes db
      runAll_ $ replicate 10 reader ++ replicate 10 (compact db)
    it "should ensure compactions with writers do not impact readers" $ withDb $ \db -> do
      let reader = reads db [Just "val", Just "new val"]
      let writer = forM_ [1..100] $ \k -> write db k "new val"
      writes db
      runAll_ $ replicate 10 reader ++ [writer] ++ replicate 10 (compact db)
  describe "compaction should preserve writes" $ do
    it "should ensure all writes are persisted" $ withDb $ \db -> do
      let writer i = forM_ [1..100] $ \k -> do
            when (k `mod` 10 == 0) $ compact db
            write db (i*100 + k) "val"
      runAll_ $ map writer [0..9]
      compact db
      compact db
      forM_ [1..1000] $ \k ->
        read db k `shouldReturn` Just "val"
