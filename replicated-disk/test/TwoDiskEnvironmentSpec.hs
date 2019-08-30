-- |

module TwoDiskEnvironmentSpec where

import           TwoDiskEnvironment
import           Test.Hspec

{-# ANN module "HLint: ingore Redundant do" #-}

should_encode_decode
  :: (Show a, Eq a) => (a -> b) -> (b -> Maybe a) -> a -> Expectation
should_encode_decode enc dec x = dec (enc x) `shouldBe` Just x

spec :: Spec
spec = do
  describe "value encoder" $ do
    it "encode >>> decode = id" $ do
      mapM_ (should_encode_decode encodeValue decodeValue)
        $ [ minBound
          , minBound + 1
          , 3
          , 1231
          , 138741923804719470
          , 2 ^ 63
          , maxBound
          , maxBound - 1
          ]
