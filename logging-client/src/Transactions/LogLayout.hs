module Transactions.LogLayout
  ( logHdrFmt
  , descriptorFmt
  ) where

import qualified Data.ByteString.Lazy as BSL
import qualified Data.ByteString as BS
import Utils.Conversion
import Data.Binary.Put (runPut, putWord32le)
import Data.Binary.Get (runGet, getWord32le)
import Data.Binary
import Control.Monad (replicateM)

import LogEncoding

-- output must be exactly blocksize bytes
toBlock :: Put -> BS.ByteString
toBlock b = let bs = BSL.toStrict (runPut b)
                padding = BS.replicate (blocksize - BS.length bs) 0 in
                if BS.length bs > blocksize
                  then error "string is already too long"
                  else BS.append bs padding

encodeLog :: LogHdr -> BS.ByteString
encodeLog (Build_LogHdr b n) =
  let binary = putWord8 (if b then 1 else 0) >> putWord32le (fromIntegral n) in
      toBlock binary

decodeLog :: BS.ByteString -> LogHdr
decodeLog bs =
  let fmt = do
        b <- getWord8
        n <- getWord32le
        return $ Build_LogHdr (b == 1) (fromIntegral n) in
    runGet fmt (BSL.fromStrict bs)

logHdrFmt :: Coq_block_encoder LogHdr
logHdrFmt = Build_block_encoder encodeLog decodeLog

encodeDesc :: Descriptor -> BS.ByteString
encodeDesc ds =
  let binary = mapM_ (putWord32le . fromIntegral) ds in
    toBlock binary

decodeDesc :: BS.ByteString -> Descriptor
decodeDesc bs =
  let fmt = replicateM blocksize (fromIntegral <$> getWord32le) in
    runGet fmt (BSL.fromStrict bs)

descriptorFmt :: Coq_block_encoder Descriptor
descriptorFmt = Build_block_encoder encodeDesc decodeDesc
