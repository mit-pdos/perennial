From RecoveryRefinement Require Import Lib.

Require Import Examples.Logging.TxnDiskAPI.
Require Import Examples.ReplicatedDisk.TwoDiskAPI.
Require Import Examples.ReplicatedDisk.OneDiskAPI.

Require Import Examples.Logging.HoareProof.
Require Import Examples.ReplicatedDisk.ReplicatedDiskImpl.

Module LoggingTwoDiskRefinement.
  Definition rf : LayerRefinement TwoDisk.TDLayer TxnD.l :=
    refinement_transitive ReplicatedDisk.Refinement_TD_OD LoggingRefinement.rf.
  Check rf.(compile_exec_seq_ok).
  Definition compile := rf.(compile).
  Definition init := rf.(init).
  Definition recover := rf.(recover).
End LoggingTwoDiskRefinement.
