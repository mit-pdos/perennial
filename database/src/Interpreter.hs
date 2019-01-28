module Interpreter
  ( interpret
  ) where

import           Control.Concurrent.Forkable
import           Control.Monad (void)
import           Control.Monad.IO.Class

import qualified Coq.BaseLayer as BaseLayer
import           Coq.Proc
import qualified DataOps
import           Filesys.Generic
import qualified FilesysOps
import           Lib (coerceRet, coerceVoid)


interpret :: (MonadFilesys m, MonadIO m, ForkableMonad m) =>
             Coq_proc (BaseLayer.Op a) x -> m x
interpret (Call (BaseLayer.FilesysOp op)) = coerceRet $ FilesysOps.interpret op
interpret (Call (BaseLayer.DataOp op)) = coerceRet . liftIO $ DataOps.interpret op
interpret (Ret x) = return x
interpret (Bind x f) = do
  r <- interpret x
  interpret (f r)
interpret (Spawn x) = do
  _ <- forkIO (void $ interpret x)
  coerceVoid $ return ()
interpret (Loop body x0) = go x0
  where go arg = do
          x <- interpret $ body arg
          case x of
            ContinueOutcome t -> go t
            DoneWithOutcome r -> return r
