module FilesystemsSpec(spec) where

import Test.Hspec
import System.Directory ( createDirectory
                        , removeDirectoryRecursive
                        , doesDirectoryExist
                        )
import Control.Monad (when)

import FilesysTests
import qualified Filesys.Memory as Mem
import qualified Filesys.Rooted as Rooted

ensureEmptyDir :: FilePath -> IO ()
ensureEmptyDir d = do
  ex <- doesDirectoryExist d
  when ex $ deleteDir d
  createDirectory d

deleteDir :: FilePath -> IO ()
deleteDir = removeDirectoryRecursive

spec :: Spec
spec = do
  describe "in-memory filesystem" $
    filesysSpec Mem.run
  describe "root directory filesystem" $
    let dir = "/tmp/test.dir" in
    before_ (ensureEmptyDir dir) . after_ (deleteDir dir) $
      filesysSpec (Rooted.run dir)
