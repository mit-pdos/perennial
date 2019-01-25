module BenchHelpers
  ( withEnv
  , benchNum
  ) where

import Criterion.Main
import Control.DeepSeq (NFData, rnf)

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
