{-# LANGUAGE OverloadedStrings #-}
module Main where

import Lib
import ExtractionExamples
import Interpreter

import Criterion.Main
import BenchHelpers
import Control.Monad (forM_, replicateM_, void)

emptyTbl :: IO (HashTable Word64 ByteString)
emptyTbl = interpret ht_setup

key :: Word64
key = 10

hashTableWrites :: [Benchmark]
hashTableWrites = writeSuite [
        ("1", interpret . ht_write1 key "value")
      , ("3", interpret . ht_write3 key "value")
      , ("hs3", \h -> do
            interpret $ ht_write1 key "value" h
            interpret $ ht_write1 (key+1) "value" h
            interpret $ ht_write1 (key+2) "value" h
            return ()
        )
      ]
  where writeSuite = map (\(name, b) -> bench name $ withEnv emptyTbl b)

hashTableReads :: [Benchmark]
hashTableReads = [
  bgroup "seq" $ readSuite [
      (1, \iters -> interpret . ht_seq_reads key iters)
      , (1000, \iters -> interpret . ht_seq_reads key iters)
      , (10000, \iters -> interpret . ht_seq_reads key iters)
      ]
  , bgroup "par" $ readSuite [
      (500, \iters -> interpret . ht_par_reads key iters)
      , (5000, \iters -> interpret . ht_par_reads key iters)
      ]
  ]
  where readSuite = map (\(num, b) ->
                           benchNum num $ \iters ->
                            withEnv filledTbl (b iters))

arrayAppends :: [Benchmark]
arrayAppends = appendSuite [
  ("1", interpret . a_append1)
  , ("3", interpret . a_append3)
  , ("hs3", \r -> do
        interpret $ a_append1 r
        interpret $ a_append1 r
        interpret $ a_append1 r
        return ())
  , ("1000", interpret . a_append_many 1000)
  , ("10000", interpret . a_append_many 10000)
  , ("hs10000", replicateM_ 10000 . interpret . a_append1)
  ]
  where appendSuite = map (\(name, b) -> bench name $ withEnvRun (interpret a_setup) b)

prepareArray :: Word64 -> IO (Array Word64)
prepareArray n = do
  r <- interpret a_setup
  interpret $ a_append_many n r
  return r

arrayReads :: [Benchmark]
arrayReads = [
  bench "read1" $ withEnvRun (prepareArray 1) $ void . interpret . a_read
  , bgroup "seq" $ readSuite [
      (1, interpret . a_readall)
      , (1000, interpret . a_readall)
      , (10000, interpret . a_readall)
      ]
  , bgroup "par" $ readSuite [
      (500, interpret . a_readall_par)
      , (5000, interpret . a_readall_par)
      ]
    ]
  where readSuite = map (\(num, b) -> benchNum num $ \iters -> withEnvRun (prepareArray iters) b)

filledTbl :: IO (HashTable Word64 ByteString)
filledTbl = do
  h <- emptyTbl
  forM_ [1..1000] $ \i ->
    interpret $ ht_write1 i "value" h
  return h

main :: IO ()
main = defaultMain [
  bgroup "hashtable" [
      bgroup "write" hashTableWrites
      , bgroup "read" hashTableReads
      ]
  , bgroup "array" [
      bgroup "append" arrayAppends
      , bgroup "reads" arrayReads
      ]
  ]
