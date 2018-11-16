module Replication.Logging where

import qualified GHC.Base
import Proc
import ComposedRefinement
import TwoDiskAPI
import TxnDiskAPI
import Disk
import Layer (InitStatus(..))

logRead :: Coq_addr -> Coq_proc (TwoDisk__Op GHC.Base.Any) Coq_block
logRead a = _LoggingTwoDiskRefinement__compile (Call (TxnD__Coq_op_read a))

logWrite :: Coq_addr -> Coq_block -> Coq_proc (TwoDisk__Op GHC.Base.Any) TxnD__WriteStatus
logWrite a b = _LoggingTwoDiskRefinement__compile (Call (TxnD__Coq_op_write a b))

logSize :: Coq_proc (TwoDisk__Op GHC.Base.Any) Integer
logSize = _LoggingTwoDiskRefinement__compile (Call TxnD__Coq_op_size)

logCommit :: Coq_proc (TwoDisk__Op GHC.Base.Any) ()
logCommit = _LoggingTwoDiskRefinement__compile (Call TxnD__Coq_op_commit)

logRecover :: Coq_proc (TwoDisk__Op GHC.Base.Any) ()
logRecover = _LoggingTwoDiskRefinement__recover

logInit :: Coq_proc (TwoDisk__Op GHC.Base.Any) InitStatus
logInit = _LoggingTwoDiskRefinement__init
