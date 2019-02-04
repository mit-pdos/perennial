{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
module Main(main) where

import           Prelude hiding (read)
import           System.CPUTime
import           Text.Printf

import           Control.Monad (replicateM, forM_, when)
import           Control.Monad.IO.Class
import qualified Data.ByteString as BS
import           Options.Applicative
import           System.Directory ( removeDirectoryRecursive
                                  , createDirectory
                                  , doesDirectoryExist)
import           System.Random

import qualified Filesys.Rooted as FS
import           SimpleDatabase

data Options =
  Options { filesysRoot :: FilePath
          , benchOptions :: BenchOptions }

opts :: Parser Options
opts = pure Options
  <*> option auto
  ( long "root"
    <> metavar "DIR"
    <> value "bench.db"
    <> help "filesystem root directory" )
  <*> benchOpts

newtype BenchOptions =
  BenchOptions{ iterations :: Int }

benchOpts :: Parser BenchOptions
benchOpts = pure BenchOptions
  <*> option auto
  ( long "iters"
    <> short 'i'
    <> value 10000
    <> showDefault
    <> help "number of iterations to run reads/writes" )

-- | timeIO runs an action and times it, reporting the result in seconds
timeIO :: MonadIO m => m () -> m Double
timeIO act = do
  start <- liftIO getCPUTime
  act
  end <- liftIO getCPUTime
  let picoSeconds = fromIntegral $ end - start
  return $ picoSeconds / 1e12

theValue :: BS.ByteString
theValue = BS.replicate 100 1

rwrite :: DbM ()
rwrite = do
  k <- liftIO randomIO
  write k theValue

fillSmall :: DbM ()
fillSmall = forM_ [1..100] $ \k -> write k theValue

rread :: DbM ()
rread = do
  k <- liftIO $ randomRIO (1, 100)
  _ <- read k
  return ()

avgTimeIO :: MonadIO m => Int -> m () -> m Double
avgTimeIO n act = do
  measurements <- replicateM n (timeIO act)
  return $ sum measurements / fromIntegral (length measurements)

timeWithUnits :: Double -> (Double, String)
timeWithUnits t
  | t < 2e-6 = (t*1e9, "ns")
  | t < 2e-3 = (t*1e6, "us")
  | t < 2.0 = (t*1e3, "ms")
  | otherwise = (t, "s")

reportTime :: MonadIO m =>
              String -> -- ^ label
              Int -> -- ^ iters
              Double -> -- ^ time (seconds)
              m ()
reportTime label iters timeSec =
  let (t, units) = timeWithUnits timeSec
      timing :: String
      timing = printf "%0.1f %s" t units in
    if iters == 1 then
      liftIO $ printf "%17s : %s\n" label timing
    else
      liftIO $ printf "%17s : %s [%d iters]\n" label timing iters

reportAvg :: MonadIO m => String -> Int -> m () -> m Double
reportAvg label iters act = do
  t <- avgTimeIO iters act
  reportTime label iters t
  return t

dbBench :: BenchOptions -> DbM ()
dbBench BenchOptions{..} = do
  let iters = iterations
  wt <- reportAvg "buffer write" iters rwrite
  fillSmall
  t <- timeIO compact
  reportTime "compaction" 1 t
  let amortizedWriteTime = (wt*fromIntegral iters + t)/fromIntegral iters
  reportTime "amortized write" iters amortizedWriteTime
  _ <- reportAvg "rbuffer read" iters rread
  compact -- make sure read buffer is empty
  _ <- reportAvg "table read" iters rread
  return ()

app :: Options -> IO ()
app Options{..} = do
  ex <- doesDirectoryExist filesysRoot
  when ex $ removeDirectoryRecursive filesysRoot
  createDirectory filesysRoot
  FS.run filesysRoot $ bracket new crash $ dbBench benchOptions
  removeDirectoryRecursive filesysRoot

main :: IO ()
main = app =<< execParser options
  where options = info opts
                  ( fullDesc
                    <> progDesc "benchmark simple database"
                    <> header "db-bench - benchmark runner for SimpleDb" )
