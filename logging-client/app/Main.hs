{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import Control.Monad (when, forM_)
import Data.Semigroup ((<>))
import Options.Applicative
import System.Directory
import System.IO

data InitOptions = InitOptions
  { defaultSizeKB :: Int
  , initDiskPaths :: (FilePath, FilePath) }

data Options = Init InitOptions

parseDiskPaths :: Parser (FilePath, FilePath)
parseDiskPaths = ((,)
                <$> argument str (metavar "FILE0")
                <*> argument str (metavar "FILE1"))
               <|> pure ("disk0.img", "disk1.img")

initOptions :: Parser InitOptions
initOptions = do
  defaultSizeKB <- option auto
    ( long "size"
      <> help "size to initialize disk files to if they do not exist"
      <> showDefault
      <> value (100*1024)
      <> metavar "KB" )
  initDiskPaths <- parseDiskPaths
  pure InitOptions {..}

diskDefaultMessage :: String
diskDefaultMessage = "disks default to disk0.img and disk1.img if not provided"

options :: Parser Options
options = hsubparser
          ( command "init" (info (Init <$> initOptions)
                               (progDesc "initialize replicated disks"
                               <> footer diskDefaultMessage))
          )

main :: IO ()
main = execParser opts >>= run
  where
    opts = info (options <**> helper)
      (fullDesc
       <> progDesc "logging over replicated disks"
       <> header "logging-client: example of using logging over replication"
       )

run :: Options -> IO ()
run (Init opts) = runInit opts

runInit :: InitOptions -> IO ()
runInit InitOptions
  { defaultSizeKB=size,
    initDiskPaths=(fn0, fn1) } = do
  exists0 <- doesFileExist fn0
  exists1 <- doesFileExist fn1
  when (not exists0 && not exists1) $
    forM_ [fn0, fn1] $ \p ->
      withFile p WriteMode $ \h ->
        hSetFileSize h (fromIntegral $ size * 1024)
