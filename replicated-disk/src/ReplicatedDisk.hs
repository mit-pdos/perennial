-- | Export the replicated disk implementations as a Haskell library

module ReplicatedDisk where

import           Interpreter
import qualified ReplicatedDiskImpl            as RD
import           TwoDiskEnvironment

type Addr = Int
type Value = Int

read :: Addr -> Proc Value
read a = interpret (RD.read a)

write :: Addr -> Value -> Proc ()
write a v = interpret (RD.write a v)

-- | recover the system following a crash
recv :: Proc ()
recv = interpret RD.recv
