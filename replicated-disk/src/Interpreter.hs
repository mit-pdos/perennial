-- | Run the base operations from the TwoDisk layer

module Interpreter
  ( interpret
  )
where

import           GHC.Exts                       ( Any )
import           Unsafe.Coerce

import qualified Proc
import           TwoDiskAPI                     ( TwoDisk__Op(..) )
import           TwoDiskEnvironment

runOp :: TwoDisk__Op a -> Proc a
runOp (TwoDisk__Read_Mem a        ) = unsafeCoerce $ readMem a
runOp (TwoDisk__Write_Mem a x     ) = unsafeCoerce $ writeMem a x
runOp (TwoDisk__CAS a old new     ) = unsafeCoerce $ casMem a old new
runOp (TwoDisk__Read_Disk did a   ) = unsafeCoerce $ readDisk did a
runOp (TwoDisk__Write_Disk did a x) = unsafeCoerce $ writeDisk did a x

interpret :: Proc.Coq_proc (TwoDisk__Op Any) a -> Proc a
interpret (Proc.Call op       ) = runOp (unsafeCoerce op)
interpret (Proc.Ret  x        ) = return x
interpret (Proc.Bind p    rx  ) = interpret p >>= unsafeCoerce (interpret . rx)
interpret (Proc.Loop body init) = go init
 where
  go val = do
    outcome <- interpret (body val)
    case outcome of
      Proc.ContinueOutcome x -> go x
      Proc.DoneWithOutcome r -> return r
interpret (Proc.Unregister) = error "normal code should not call unregister"
interpret (Proc.Wait      ) = error "normal code should not call wait"
interpret (Proc.Spawn p   ) = unsafeCoerce $ forkProc (interpret p)
