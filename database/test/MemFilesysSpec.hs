module MemFilesysSpec where

import Test.Hspec

import FilesysTests
import qualified Filesys.Memory as Mem

{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

spec :: Spec
spec = do
  describe "in-memory filesystem" $
    filesysSpec Mem.run
