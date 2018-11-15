module Utils.Conversion where

import Disk (blockbytes, Coq_addr)

-- size of a block in bytes
blocksize :: Num a => a
blocksize = fromIntegral blockbytes

type FileOffset = Integer

addrToOffset :: Coq_addr -> FileOffset
addrToOffset a = a * blockbytes
