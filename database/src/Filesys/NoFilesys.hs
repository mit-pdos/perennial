{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Filesys.NoFilesys
  ( NoFilesysM(..)
  ) where

import Filesys.Generic
import Control.Monad.IO.Class
import Control.Concurrent.Forkable

newtype NoFilesysM a = NoFilesysM { run :: IO a }
  deriving (Functor, Applicative, Monad, MonadIO, ForkableMonad)

oops :: a
oops = error "invalid use of filesystem in NoFilesysM"

instance MonadFilesys NoFilesysM where
  open = oops
  close = oops
  list = oops
  size = oops
  readAt = oops
  create = oops
  append = oops
  delete = oops
  ftruncate = oops
  rename = oops
  atomicCreate = oops
