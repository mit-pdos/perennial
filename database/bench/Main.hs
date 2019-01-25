{-# LANGUAGE OverloadedStrings #-}
module Main where

import Lib
import ExtractionExamples
import Interpreter

import Criterion.Main
import BenchHelpers
import Control.Monad (forM_)

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

filledTbl :: IO (HashTable Word64 ByteString)
filledTbl = do
  h <- emptyTbl
  forM_ [1..1000] $ \i ->
    interpret $ ht_write1 i "value" h
  return h

main :: IO ()
main = defaultMain [
  bgroup "write" hashTableWrites
  , bgroup "read" hashTableReads
  ]
