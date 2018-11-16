{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import           Control.Monad.IO.Class (liftIO)
import           Data.Semigroup ((<>))
import           Options.Applicative
import           Replication.Logging
import           Replication.TwoDiskEnvironment
import qualified Replication.TwoDiskOps as TD
import           Transactions.LogEncoding (encodeNum, decodeNum)
import           TxnDiskAPI (TxnD__WriteStatus(..))

newtype CommonOpts = CommonOpts
  { diskPaths :: (FilePath, FilePath) }

newtype InitOptions = InitOptions
  { defaultSizeKB :: Int }

parseDiskPaths :: Parser (FilePath, FilePath)
parseDiskPaths = liftA2 (,)
  (option auto ( long "disk0" <> help "filename for first disk" <> showDefault <> value "disk0.img" ))
  (option auto ( long "disk1" <> help "filename for second disk" <> showDefault <> value "disk1.img" ))

parseCommonOpts :: Parser CommonOpts
parseCommonOpts = CommonOpts <$> parseDiskPaths

initOptions :: Parser InitOptions
initOptions = do
  defaultSizeKB <- option auto
    ( long "size"
      <> help "size (in KB) to initialize disk files to if they do not exist"
      <> showDefault
      <> value 1024
      <> metavar "KB" )
  pure InitOptions {..}

data WriteOptions = WriteOptions
  { writeAddr :: Int
  , writeValue :: Int }

newtype ReadOptions = ReadOptions
  { readAddr :: Int }

writeOptions :: Parser WriteOptions
writeOptions = do
  writeAddr <- argument auto (metavar "ADDR")
  writeValue <- argument auto (metavar "VALUE")
  pure WriteOptions {..}

readOptions :: Parser ReadOptions
readOptions = do
  readAddr <- argument auto (metavar "ADDr")
  pure ReadOptions {..}

data CommitOptions = CommitOptions{}

commitOptions :: Parser CommitOptions
commitOptions = pure CommitOptions

data RecoverOptions = RecoverOptions{}

recoverOptions :: Parser RecoverOptions
recoverOptions = pure RecoverOptions

data CmdOpts =
  Init InitOptions
  | Write WriteOptions
  | Read ReadOptions
  | Commit CommitOptions
  | Recover RecoverOptions

type Options = (CommonOpts, CmdOpts)

diskDefaultMessage :: String
diskDefaultMessage = "disks default to disk0.img and disk1.img if not provided"

options :: Parser Options
options = do
  common <- parseCommonOpts
  cmd <- hsubparser
          ( command "init" (info (Init <$> initOptions)
                               (progDesc "initialize replicated disks"
                               <> footer diskDefaultMessage))
            <> command "write" (info
                                (Write <$> writeOptions)
                                (progDesc "add to current transaction"))
            <> command "read" (info
                                (Read <$> readOptions)
                                (progDesc "read from committed state"))
            <> command "commit" (info
                                (Commit <$> commitOptions)
                                (progDesc "commit current transaction"))
            <> command "recover" (info
                                (Recover <$> recoverOptions)
                                (progDesc "run recovery"))
          )
  pure (common, cmd)

main :: IO ()
main = execParser opts >>= run
  where
    opts = info (options <**> helper)
      (fullDesc
       <> progDesc "logging over replicated disks"
       <> header "logging-client: example of using logging over replication"
       )

run :: Options -> IO ()
run (CommonOpts{diskPaths=(fn0, fn1)},
     Init InitOptions{defaultSizeKB=size}) = do
  env <- TD.init fn0 fn1 (fromIntegral size*1024)
  runTD env . TD.interpret $ logInit
  return ()
run (opts, Write WriteOptions{..}) =
  let a = fromIntegral writeAddr
      v = encodeNum writeValue in
    runCmd opts $ do
      s <- TD.interpret (logWrite a v)
      case s of
        TxnD__WriteOK -> return ()
        TxnD__WriteErr -> liftIO $ putStrLn "write failed!"
run (opts, Read ReadOptions{..}) =
  let a = fromIntegral readAddr in
    runCmd opts $ do
      v <- TD.interpret (logRead a)
      liftIO $ print (decodeNum v)
run (opts, Commit CommitOptions) =
  runCmd opts $ TD.interpret logCommit
run (opts, Recover RecoverOptions) =
  runCmd opts $ TD.interpret logRecover

runCmd :: CommonOpts -> Proc a -> IO a
runCmd CommonOpts{diskPaths=(fn0, fn1)} p = do
  env <- newEnv fn0 fn1
  runTD env p
