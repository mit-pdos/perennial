module FilesysOps
  ( Env(..)
  , FilesysM
  , interpret
  ) where

import Control.Monad.Reader (ReaderT)

import Filesys

-- TODO: add filesystem root path
data Env = Env { }

type FilesysM = ReaderT Env IO

interpret :: FS__Op x -> FilesysM x
interpret = error "filesystem ops are unimplemented"
