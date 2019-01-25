{-# LANGUAGE OverloadedStrings #-}
module Main where

import Lib
import ExtractionExamples
import Interpreter

import Criterion.Main
import Control.DeepSeq (NFData, rnf)
import Control.Monad (forM_)

newtype HashTableEnv =
  HashTableEnv { table :: HashTable Word64 ByteString }

instance NFData HashTableEnv where
  rnf _ = ()

emptyTbl :: IO HashTableEnv
emptyTbl = HashTableEnv <$> interpret ex1_setup

filledTbl :: IO HashTableEnv
filledTbl = do
  h <- emptyTbl
  forM_ [1..1000] $ \i ->
    interpret $ ex1_write1 i "value" (table h)
  return h

tableEnv :: IO HashTableEnv -> (HashTable Word64 ByteString -> IO ()) -> Benchmarkable
tableEnv mkTable b = perBatchEnv (const mkTable) (b . table)

benchNum :: (Show int, Integral int) =>
            int -> (int -> Benchmarkable) -> Benchmark
benchNum iters b = bench (show iters) (b iters)

main :: IO ()
main = defaultMain [
    bgroup "write" [
        bench "1" $ tableEnv emptyTbl $ interpret . ex1_write1 1 "value"
        , bench "3" $ tableEnv emptyTbl $ interpret . ex1_write3 1 "value"
        , bench "hs3" $ tableEnv emptyTbl $ \h -> do
            interpret $ ex1_write1 1 "value" h
            interpret $ ex1_write1 1 "value" h
            interpret $ ex1_write1 1 "value" h
        ]
  , bgroup "read" [
        bgroup "seq" [
            benchNum 1 $ \iters -> tableEnv filledTbl $
              interpret . ex2_seq_reads 1 iters
          , benchNum 1000 $ \iters -> tableEnv filledTbl $
            interpret . ex2_seq_reads 1 iters
          , benchNum 10000 $ \iters -> tableEnv filledTbl $
            interpret . ex2_seq_reads 1 iters
          ]
      , bgroup "par" [
            benchNum 500 $ \iters -> tableEnv filledTbl $
              interpret . ex2_par_reads 1 iters
          , benchNum 5000 $ \iters -> tableEnv filledTbl $
            interpret . ex2_par_reads 1 iters
          ]
      ]
  ]
