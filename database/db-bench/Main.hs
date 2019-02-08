{-# LANGUAGE RecordWildCards, NamedFieldPuns, DuplicateRecordFields #-}
module Main(main) where

import           Prelude hiding (read)
import           System.CPUTime
import           Text.Printf
import           Control.Concurrent.MVar (newEmptyMVar, putMVar, tryTakeMVar)

import           Control.Concurrent.Forkable
import           Control.Monad (replicateM, replicateM_, forM_, when)
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
          , benchCmd :: Command }

opts :: Parser Options
opts = pure Options
  <*> option str
  ( long "root"
    <> metavar "DIR"
    <> value "bench.db"
    <> help "filesystem root directory" )
  <*> hsubparser
  ( command "fillread" (info fillReadOpts
                        (progDesc "run fill + read benchmarks"))
    <> command "fillcompact" (info fillCompactOpts
                             (progDesc "concurrent fill + compact benchmark"))
    <> command "readcompact" (info readCompactOpts
                             (progDesc "concurrent read + compact benchmark"))
    <> command "parread" (info parReadOpts
                           (progDesc "parallel readers"))
  )

-- TODO: don't really need different records for options, can be unified
data Command = FillReadBench FillReadOptions
             | FillCompactBench FillCompactOptions
             | ReadCompactBench ReadCompactOptions
             | ParReadBench ParReadOptions

newtype FillReadOptions =
  FillReadOptions{ iterations :: Int }

data FillCompactOptions =
  FillCompactOptions{ iterations :: Int
                    , numKeys :: Int }

data ReadCompactOptions =
  ReadCompactOptions{ iterations :: Int
                    , numKeys :: Int
                    , parReaders :: Int }

data ParReadOptions =
  ParReadOptions{ iterations :: Int
                , parReaders :: Int
                }

fillReadOpts :: Parser Command
fillReadOpts = FillReadBench <$> opts
  where opts = pure FillReadOptions <*> iterOpt

fillCompactOpts :: Parser Command
fillCompactOpts = FillCompactBench <$> opts
  where opts = pure FillCompactOptions <*> iterOpt <*> dbSizeOpt

readCompactOpts :: Parser Command
readCompactOpts = ReadCompactBench <$> opts
  where opts = pure ReadCompactOptions <*> iterOpt <*> dbSizeOpt <*> parReadersOpt

parReadOpts :: Parser Command
parReadOpts = ParReadBench <$> opts
  where opts = pure ParReadOptions <*> iterOpt <*> parReadersOpt

iterOpt :: Parser Int
iterOpt = option auto
  ( long "iters"
    <> short 'i'
    <> value 10000
    <> showDefault
    <> help "number of iterations to run reads/writes" )

dbSizeOpt :: Parser Int
dbSizeOpt = option auto
  ( long "db-size"
    <> value 100
    <> showDefault
    <> help "maximum number of keys in database" )

parReadersOpt :: Parser Int
parReadersOpt = option auto
  ( long "par"
    <> value 2
    <> showDefault
    <> help "number of parallel reader threads" )

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
              Double -> -- ^ time/iteration (seconds)
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

fillReadBench :: FillReadOptions -> DbM ()
fillReadBench FillReadOptions{..} = do
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

whileCompacting :: DbM a -> DbM (a, Int)
whileCompacting act = do
  m <- liftIO newEmptyMVar
  _ <- forkIO $ do
    x <- act
    liftIO $ putMVar m x
  let compactTillDone n = do
        compact
        r <- liftIO $ tryTakeMVar m
        case r of
          Just x -> return (x, n)
          Nothing -> compactTillDone (n+1)
  compactTillDone 0

fillCompactBench :: FillCompactOptions -> DbM ()
fillCompactBench FillCompactOptions{..} = do
  let iters = iterations
  let sizedWrite = do
        k <- liftIO $ randomRIO (1, fromIntegral numKeys)
        write k theValue
  (ts, numCompactions) <- whileCompacting $ replicateM iters (timeIO sizedWrite)
  reportTime "write with compactions" iters (sum ts / fromIntegral iters)
  liftIO $ printf "  (finished %d compactions)\n" numCompactions

spawn :: (ForkableMonad m, MonadIO m) => m a -> m (MVar a)
spawn act = do
  m <- liftIO newEmptyMVar
  _ <- forkIO $ act >>= liftIO . putMVar m
  return m

writeTable :: Int -> -- ^ number of keys
              DbM ()
writeTable numKeys = do
  forM_ [1..fromIntegral numKeys] $ \k -> write k theValue
  compact
  compact

parReads :: Int -> -- ^ par
            Int -> -- ^ iters
            DbM [Double]
parReads par iters = do
  let reads = timeIO $ replicateM_ iters rread
  ms <- replicateM par $ spawn reads
  mapM (liftIO . takeMVar) ms

parReadBench :: ParReadOptions -> DbM ()
parReadBench ParReadOptions{..} = do
  let iters = iterations
  let numKeys = 100
  writeTable numKeys
  ts <- parReads parReaders iters
  let totalIters = iters * parReaders
  reportTime "reads" totalIters (sum ts / fromIntegral totalIters)

readCompactBench :: ReadCompactOptions -> DbM ()
readCompactBench ReadCompactOptions{..} = do
  let iters = iterations
  writeTable numKeys
  (ts, numCompactions) <- whileCompacting $ parReads parReaders iters
  let totalIters = iters * parReaders
  reportTime "reads with compactions" totalIters (sum ts / fromIntegral totalIters)
  liftIO $ printf "  (finished %d compactions)\n" numCompactions

runBench :: Command -> DbM ()
runBench (FillReadBench opts) = fillReadBench opts
runBench (FillCompactBench opts) = fillCompactBench opts
runBench (ReadCompactBench opts) = readCompactBench opts
runBench (ParReadBench opts) = parReadBench opts

app :: Options -> IO ()
app Options{..} = do
  ex <- doesDirectoryExist filesysRoot
  when ex $ removeDirectoryRecursive filesysRoot
  createDirectory filesysRoot
  FS.run filesysRoot $ bracket new crash $ runBench benchCmd
  removeDirectoryRecursive filesysRoot

main :: IO ()
main = app =<< execParser options
  where options = info (opts <**> helper)
                  ( fullDesc
                    <> progDesc "benchmark simple database"
                    <> header "db-bench - benchmark runner for SimpleDb" )
