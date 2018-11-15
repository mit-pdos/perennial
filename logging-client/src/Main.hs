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

data Options = Start ServerOptions
             | Init InitOptions

parseDiskPaths :: Parser (FilePath, FilePath)
parseDiskPaths = ((,)
                <$> argument str (metavar "FILE0")
                <*> argument str (metavar "FILE1"))
               <|> pure ("disk0.img", "disk1.img")

serverOptions :: Parser ServerOptions
serverOptions = do
  diskPaths <- parseDiskPaths
  logCommands <- switch (long "debug"
                        <> short 'd'
                        <> help "log each operation received")
  pure ServerOptions {..}

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
          ( command "start" (info (Start <$> serverOptions)
                             (progDesc "start server"
                             <> footer diskDefaultMessage))
            <> command "init" (info (Init <$> initOptions)
                               (progDesc "initialize replicated disks"
                               <> footer diskDefaultMessage))
          )

main :: IO ()
main = execParser opts >>= run
  where
    opts = info (options <**> helper)
      (fullDesc
       <> progDesc "an nbd server that replicates over two disks; COMMAND is either init or start"
       <> header "replicate-nbd - replicating network block device"
       )

run :: Options -> IO ()
run (Start opts) = runServer opts
run (Init opts) = runInit opts

runInit :: InitOptions -> IO ()
runInit InitOptions
  { defaultSizeKB=size,
    initDiskPaths=diskPaths@(fn0, fn1) } = do
  exists0 <- doesFileExist fn0
  exists1 <- doesFileExist fn1
  when (not exists0 && not exists1) $
    forM_ [fn0, fn1] $ \p ->
      withFile p WriteMode $ \h ->
        hSetFileSize h (fromIntegral $ size * 1024)
  initServer diskPaths
