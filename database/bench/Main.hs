{-# LANGUAGE OverloadedStrings #-}
module Main where

import Lib
import ExtractionExamples
import Interpreter

import Criterion.Main
import Control.DeepSeq (NFData, rnf)
import Control.Monad (forM_)

emptyTbl :: IO (HashTable Word64 ByteString)
emptyTbl = interpret ex1_setup

filledTbl :: IO (HashTable Word64 ByteString)
filledTbl = do
  h <- emptyTbl
  forM_ [1..1000] $ \i ->
    interpret $ ex1_write1 i "value" h
  return h

newtype EnvWrapper a =
  EnvWrapper { getEnv :: a }

instance NFData (EnvWrapper a) where
  rnf _ = ()

-- like perBatchEnv but without any constraints on env
-- (and somewhat simplified types)
withEnv :: IO env -> (env -> IO ()) -> Benchmarkable
withEnv mkTable b =
  perBatchEnv (const (EnvWrapper <$> mkTable)) (b . getEnv)

benchNum :: (Show int, Integral int) =>
            int -> (int -> Benchmarkable) -> Benchmark
benchNum iters b = bench (show iters) (b iters)

main :: IO ()
main = defaultMain [
    bgroup "write" [
        bench "1" $ withEnv emptyTbl $ interpret . ex1_write1 1 "value"
        , bench "3" $ withEnv emptyTbl $ interpret . ex1_write3 1 "value"
        , bench "hs3" $ withEnv emptyTbl $ \h -> do
            interpret $ ex1_write1 1 "value" h
            interpret $ ex1_write1 1 "value" h
            interpret $ ex1_write1 1 "value" h
        ]
  , bgroup "read" [
        bgroup "seq" [
            benchNum 1 $ \iters -> withEnv filledTbl $
              interpret . ex2_seq_reads 1 iters
          , benchNum 1000 $ \iters -> withEnv filledTbl $
            interpret . ex2_seq_reads 1 iters
          , benchNum 10000 $ \iters -> withEnv filledTbl $
            interpret . ex2_seq_reads 1 iters
          ]
      , bgroup "par" [
            benchNum 500 $ \iters -> withEnv filledTbl $
              interpret . ex2_par_reads 1 iters
          , benchNum 5000 $ \iters -> withEnv filledTbl $
            interpret . ex2_par_reads 1 iters
          ]
      ]
  ]
