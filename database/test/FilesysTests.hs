{-# LANGUAGE RankNTypes #-}
module FilesysTests
  ( filesysSpec
  ) where

import           Control.Monad.IO.Class
import qualified Data.ByteString as BS
import           Test.Hspec hiding (shouldReturn)

import           Filesys.Generic
import           Lib (ByteString, Fd)

{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

makeFile :: MonadFilesys m => FilePath -> ByteString -> m ()
makeFile p bs = do
  fd <- create p
  append fd bs
  close fd

withFile :: MonadFilesys m => FilePath -> (Fd -> m a) -> m a
withFile p act = do
  fd <- open p
  act fd <* close fd

readAll :: MonadFilesys m => FilePath -> m ByteString
readAll p = withFile p $ \fd -> readAt fd 0 1000

shouldReturn :: (HasCallStack, Show a, Eq a, MonadIO m) =>
                m a -> a -> m ()
shouldReturn act expected = do
  x <- act
  liftIO $ x `shouldBe` expected

filesysSpec :: (MonadFilesys m, MonadIO m) =>
               (forall a. m a -> IO a) -> Spec
filesysSpec run = do
  describe "basic data ops" $ do
    it "should initialize correctly" $ do
      run $ return ()
    it "should open and close a file" $ run $ do
      create "foo" >>= close
    it "should create an empty file" $ run $ do
      create "foo" >>= close
      bs <- readAll "foo"
      liftIO $ bs `shouldBe` ""
    it "should use distinct fds" $ run $ do
      fd1 <- create "file1"
      fd2 <- create "file2"
      liftIO $ fd2 `shouldNotBe` fd1
    it "should write data" $ run $ do
      makeFile "file" "some data"
    it "should read back written data" $ run $ do
      makeFile "file" "some data"
      fd <- open "file"
      readAt fd 0 100 `shouldReturn` "some data"
  describe "other operations" $ do
    it "should report size" $ run $ do
      makeFile "file" "some data"
      let expected = fromIntegral $ BS.length "some data"
      withFile "file" size `shouldReturn` expected
    it "should read from the middle" $ run $ do
      makeFile "file" "some data"
      spc <- withFile "file" $ \fh -> readAt fh 4 1
      liftIO $ spc `shouldBe` " "
    it "should append data" $ run $ do
      fd <- create "f"
      append fd "hello"
      append fd " world"
      close fd
      readAll "f" `shouldReturn` "hello world"
    it "should rename files" $ run $ do
      makeFile "f1" "original"
      rename "f1" "f2"
      readAll "f2" `shouldReturn` "original"
    it "should overwrite on rename" $ run $ do
      makeFile "f1" "overwrite"
      makeFile "f2" "old data"
      rename "f1" "f2"
      readAll "f2" `shouldReturn` "overwrite"
    it "should atomicCreate correctly" $ run $ do
      atomicCreate "f" "important data"
      readAll "f" `shouldReturn` "important data"
    it "should list files" $ run $ do
      mapM_ (`makeFile` "") ["f1", "f2", "f3"]
      files <- list
      liftIO $ files `shouldMatchList` ["f1", "f2", "f3"]
    it "should delete files" $ run $ do
      makeFile "f1" "data"
      makeFile "f2" "data"
      listing1 <- list
      liftIO $ listing1 `shouldMatchList` ["f1", "f2"]
      delete "f1"
      list `shouldReturn` ["f2"]
    it "should truncate files" $ run $ do
      makeFile "f1" "data"
      ftruncate "f1"
      readAll "f1" `shouldReturn` ""
      withFile "f1" size `shouldReturn` 0
