{-# LANGUAGE OverloadedStrings #-}
module DataStructureSpec(spec) where

import           Test.Hspec

import qualified Coq.BaseLayer as BaseLayer
import           Coq.DataStructureTests
import           Coq.Proc (Coq_proc)
import qualified Filesys.NoFilesys as NoFilesys
import           Interpreter

{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

run :: Coq_proc (BaseLayer.Op a) x -> IO x
run = NoFilesys.run . interpret

runTest :: (HasCallStack, Eq a, Show a) => Coq_proc (BaseLayer.Op x) (a, a) -> Expectation
runTest p = do
  (actual, expected) <- run p
  actual `shouldBe` expected

spec :: Spec
spec = parallel $ do
  describe "iorefs" $ do
    it "should read" $ do
      runTest $ iorefRead "foo"
    it "should write" $ do
      runTest $ iorefWrite "foo"
  describe "arrays" $ do
    it "should get length" $ do
      runTest arrayLength
    it "should get values" $ do
      runTest arrayGet
  describe "hashtables" $ do
    it "should lookup" $ do
      runTest $ hashtableLookup "bar"
    it "should lookup ints" $ do
      runTest $ hashtableIntLookup
    it "should read all elements" $ do
      runTest hashtableReadAll
  describe "locks" $ do
    it "should not deadlock" $ do
      runTest locking
