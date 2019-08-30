module TwoDiskEnvironmentSpec where

import           Control.Exception
import           Control.Monad.Trans
import           System.Directory
import           Test.Hspec

import           TwoDiskAPI                     ( TwoDisk__Coq_diskId(..) )
import           TwoDiskEnvironment

{-# ANN module "HLint: ignore Redundant do" #-}

shouldEncodeDecode
  :: (Show a, Eq a) => (a -> b) -> (b -> Maybe a) -> a -> Expectation
shouldEncodeDecode enc dec x = dec (enc x) `shouldBe` Just x

shouldProduce :: (Show a, Eq a) => Proc a -> a -> Proc ()
shouldProduce comp x = do
  actual <- comp
  liftIO $ actual `shouldBe` x

withEnv :: Proc a -> IO a
withEnv act = bracket (newEnv "/tmp/disk")
                      (\env -> closeEnv env >> deleteEnv env)
                      (\env -> runProc env act)

d0 :: TwoDisk__Coq_diskId
d0 = TwoDisk__Coq_d0

d1 :: TwoDisk__Coq_diskId
d1 = TwoDisk__Coq_d1

spec :: Spec
spec = do
  describe "value encoder" $ do
    it "encode >>> decode = id" $ do
      mapM_
        (shouldEncodeDecode encodeValue decodeValue)
        [ minBound
        , minBound + 1
        , 3
        , 1231
        , 138741923804719470
        , 2 ^ 63
        , maxBound
        , maxBound - 1
        ]
  describe "two disk environment" $ do
    it "can be setup and closed" $ withEnv $ do
      return ()
    it "can handle reads and writes" $ withEnv $ do
      readMem 0 `shouldProduce` 0
      writeMem 0 32
      writeMem 1 7
      readMem 0 `shouldProduce` 32
      writeMem 0 3
      readMem 0 `shouldProduce` 3
      readMem 1 `shouldProduce` 7
    it "can compare and swap" $ withEnv $ do
      writeMem 0 100
      casMem 0 0 1 `shouldProduce` 100
      readMem 0 `shouldProduce` 100
      casMem 0 100 1 `shouldProduce` 100
      readMem 0 `shouldProduce` 1
    it "can handle disk reads and writes" $ withEnv $ do
      readDisk d0 0 `shouldProduce` Just 0
      writeDisk d0 0 32
      writeDisk d1 0 132
      writeDisk d0 1 7
      writeDisk d1 1 107
      readDisk d0 0 `shouldProduce` Just 32
      writeDisk d0 0 3
      readDisk d0 0 `shouldProduce` Just 3
      readDisk d1 0 `shouldProduce` Just 132
      readDisk d0 1 `shouldProduce` Just 7
      readDisk d1 1 `shouldProduce` Just 107
    it "can write to 999" $ withEnv $ do
      writeMem 999 100
      readMem 999 `shouldProduce` 100
      writeDisk d0 999 100
      writeDisk d1 999 100
      readDisk d0 999 `shouldProduce` Just 100
      readDisk d1 999 `shouldProduce` Just 100
    it "can handle disk failures" $ withEnv $ do
      writeDisk d0 0 32
      writeDisk d1 0 132
      readDisk d0 0 `shouldProduce` Just 32
      readDisk d1 0 `shouldProduce` Just 132
      liftIO $ removeFile "/tmp/disk.0"
      readDisk d0 0 `shouldProduce` Nothing
      readDisk d1 0 `shouldProduce` Just 132
