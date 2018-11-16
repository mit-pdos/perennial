{-# LANGUAGE StandaloneDeriving #-}
module LogEncodingSpec where

import Transactions.LogEncoding
import LogEncoding
import Data.Bits

import Test.Hspec

{-# ANN module "HLint: ingore Redundant do" #-}

should_encode_decode :: (Show a, Eq a) => Coq_block_encoder a -> a -> Expectation
should_encode_decode (Build_block_encoder enc dec) x = dec (enc x) `shouldBe` x

deriving instance Show LogHdr
deriving instance Eq LogHdr

spec :: Spec
spec = do
  describe "log encoder" $ do
    it "encode >>> decode = id" $ do
      mapM_ (should_encode_decode logHdrFmt) $
        [ Build_LogHdr True 3
        , Build_LogHdr False 0
        , Build_LogHdr True 230 ]
  describe "descriptor encoder" $ do
    it "encode >>> decode = id" $ do
      let len = fromIntegral coq_LOG_LENGTH in
        mapM_ (should_encode_decode descriptorFmt) $
          [ replicate len 3
          , replicate len 0
          , replicate len (shift 1 30)
          , replicate 10 3 ++
            replicate 120 7 ++
            replicate (len-10-120) (shift 1 20)]
