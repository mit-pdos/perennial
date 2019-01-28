module LibSpec(spec) where

import qualified Data.ByteString as BS
import           Test.Hspec
import           Test.QuickCheck
import           Test.QuickCheck.Instances.ByteString ()

import           Lib

{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

genAscii :: Gen Char
genAscii = elements ['a'..'z']

genAsciiStr :: Gen String
genAsciiStr = listOf genAscii

spec :: Spec
spec = parallel $ do
  describe "bytestring-string conversions" $ do
    it "should roundtrip normal strings" $ property $
      forAll genAsciiStr $ \s ->
      (byteString_to_String . string_to_ByteString) s == s
    it "should roundtrip bytestrings" $ property $
      \x -> (string_to_ByteString . byteString_to_String) x == x
  describe "uint64 LE encoding" $ do
    it "should roundtrip" $ property $
      \x -> (uint64_from_le . uint64_to_le) x == Just x
  it "take ++ drop should be whole string" $ property $
    \bs n -> BS.take n bs `BS.append` BS.drop n bs == bs
