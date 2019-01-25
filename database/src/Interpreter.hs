module Interpreter
  ( interpret
  ) where

import qualified GHC.Base
import Control.Concurrent (forkIO)
import Control.Monad (void)

--import qualified FilesysOps
import qualified DataOps

import Proc
import qualified BaseLayer
import DataStructures

interpret :: Coq_proc (BaseLayer.Op GHC.Base.Any) x -> IO x
interpret (Call (BaseLayer.FilesysOp _)) = error "filesystem ops not wired in"
interpret (Call (BaseLayer.DataOp op)) = unsafeCoerce <$> DataOps.interpret op
interpret (Ret x) = return x
interpret (Bind x f) = interpret x >>= interpret . f
interpret (Spawn x) =
  let spawnedThread = void $ interpret x in
  unsafeCoerce <$> forkIO spawnedThread
interpret (Loop body x0) = do
  x <- interpret $ body x0
  case x of
    ContinueOutcome t -> interpret (Loop body t)
    DoneWithOutcome r -> return r
