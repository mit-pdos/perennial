module SimpleDbConcurrentSpec(spec) where

import Prelude hiding (read)

import Control.Concurrent.Forkable
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import Control.Monad (forM, forM_, replicateM_, mapM, void)
import Control.Monad.IO.Class
import Test.Hspec

import SimpleDbTesting

{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

runAll :: (ForkableMonad m, MonadIO m) => [m a] -> m [a]
runAll acts = do
  mvars <- forM acts $ \act -> do
    m <- liftIO newEmptyMVar
    _ <- forkIO (act >>= liftIO . putMVar m)
    return m
  mapM (liftIO . takeMVar) mvars

runAll_ :: (ForkableMonad m, MonadIO m) => [m a] -> m ()
runAll_ acts = void $ runAll acts

spec :: Spec
spec = do
  describe "concurrent operations should not crash" $ do
    let writeThread db = forM_ [1..100] $ \k -> write db k "val"
    let readThread db = forM_ [1..100] $ read db
    let compactThread db = replicateM_ 100 $ compact db
    it "should handle concurrent reads" $ withDb $ \db -> do
      writeThread db
      runAll_ $ replicate 10 $ readThread db
    it "should handle concurrent writes" $ withDb $ \db -> do
      runAll_ $ replicate 10 $ writeThread db
    it "should handle mixed reads, writes" $ withDb $ \db -> do
      runAll_ $ concat $ replicate 10 [readThread db, writeThread db]
    it "should handle reads, writes, and compactions" $ withDb $ \db -> do
      runAll_ $ [readThread db, compactThread db] ++ replicate 10 (writeThread db)
