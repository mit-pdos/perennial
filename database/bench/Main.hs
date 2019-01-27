{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Monad (forM_, replicateM_, void)

import           Criterion.Main

import qualified BaseLayer
import           BenchHelpers
import           ExtractionExamples
import qualified Filesys.NoFilesys as NoFilesys
import           Interpreter
import           Lib
import           Proc (Coq_proc)

run :: Coq_proc (BaseLayer.Op a) x -> IO x
run = NoFilesys.run . interpret

emptyTbl :: IO (HashTable Word64 ByteString)
emptyTbl = run ht_setup

key :: Word64
key = 10

hashTableWrites :: [Benchmark]
hashTableWrites = writeSuite
  [ ("1", run . ht_write1 key "value")
  , ("3", run . ht_write3 key "value")
  , ("hs3", \h -> do
        run $ ht_write1 key "value" h
        run $ ht_write1 (key+1) "value" h
        run $ ht_write1 (key+2) "value" h
        return ()
    )
  ]
  where
    writeSuite = map $ \(name, b) ->
      bench name $ withEnv emptyTbl b

hashTableReads :: [Benchmark]
hashTableReads =
  [ bgroup "seq" $ readSuite
    [ (1, \iters -> run . ht_seq_reads key iters)
    , (1000, \iters -> run . ht_seq_reads key iters)
    , (10000, \iters -> run . ht_seq_reads key iters)
    ]
  , bgroup "par" $ readSuite
    [ (500, \iters -> run . ht_par_reads key iters)
    , (5000, \iters -> run . ht_par_reads key iters)
    ]
  ]
  where
    readSuite = map $ \(num, b) ->
      benchNum num $ \iters -> withEnv filledTbl (b iters)

arrayAppends :: [Benchmark]
arrayAppends = appendSuite
  [ ("1", run . a_append1)
  , ("3", run . a_append3)
  , ("hs3", \r -> do
        run $ a_append1 r
        run $ a_append1 r
        run $ a_append1 r
        return ())
  , ("1000", run . a_append_many 1000)
  , ("10000", run . a_append_many 10000)
  , ("hs10000", replicateM_ 10000 . run . a_append1)
  ]
  where
    appendSuite = map $ \(name, b) ->
      bench name $ withEnvRun (run a_setup) b

prepareArray :: Word64 -> IO (Array Word64)
prepareArray n = do
  r <- run a_setup
  run $ a_append_many n r
  return r

arrayReads :: [Benchmark]
arrayReads =
  [ bench "read1" $ withEnvRun (prepareArray 1) $ void . run . a_read
  , bgroup "seq" $ readSuite
    [ (1, run . a_readall)
    , (1000, run . a_readall)
    , (10000, run . a_readall)
    ]
  , bgroup "par" $ readSuite
    [ (500, run . a_readall_par)
    , (5000, run . a_readall_par)
    ]
  ]
  where
    readSuite = map $ \(num, b) ->
      benchNum num $ \iters -> withEnvRun (prepareArray iters) b

prepareRef :: IO (IORef ByteString)
prepareRef = run (ref_setup "string")

iorefBenches :: [Benchmark]
iorefBenches =
  [ bench "write" $ withEnv prepareRef $ run . ref_write "new string"
  , bgroup "read"
    [ bench "1" $ withEnv prepareRef $ run . ref_read
    , bgroup "seq" $ iorefSuite
      [ (1, \iters -> run . ref_read_seq iters)
      , (100000, \iters -> run . ref_read_seq iters)
      ]
    , bgroup "par" $ iorefSuite
      [ (1, \iters -> run . ref_read_par iters)
      , (50000, \iters -> run . ref_read_par iters)
      ]
    ]
  ]
  where
    iorefSuite = map $ \(num, b) ->
      benchNum num $ \iters -> withEnv prepareRef (b iters)

filledTbl :: IO (HashTable Word64 ByteString)
filledTbl = do
  h <- emptyTbl
  forM_ [1..1000] $ \i ->
    run $ ht_write1 i "value" h
  return h

main :: IO ()
main = defaultMain
  [ bgroup "ioref" iorefBenches
  , bgroup "hashtable"
    [ bgroup "write" hashTableWrites
    , bgroup "read" hashTableReads
    ]
  , bgroup "array"
    [ bgroup "append" arrayAppends
    , bgroup "reads" arrayReads
    ]
  ]
