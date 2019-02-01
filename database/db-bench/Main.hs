{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
module Main(main) where

import qualified Filesys.Rooted as FS
import Options.Applicative
import SimpleDatabase

data Options =
  Options { filesysRoot :: FilePath
          , benchOptions :: BenchOptions }

data BenchOptions =
  BenchOptions{}

opts :: Parser Options
opts = pure Options
  <*> strOption
  ( long "root"
    <> metavar "DIR"
    <> value "bench.db"
    <> help "filesystem root directory" )
  <*> benchOpts

benchOpts :: Parser BenchOptions
benchOpts = pure BenchOptions

dbBench :: BenchOptions -> DbM ()
dbBench BenchOptions = return ()

app :: Options -> IO ()
app Options{..} = FS.run filesysRoot $ bracket new close $ dbBench benchOptions

main :: IO ()
main = app =<< execParser options
  where options = info opts
                  ( fullDesc
                    <> progDesc "benchmark simple database"
                    <> header "db-bench - benchmark runner for SimpleDb" )
