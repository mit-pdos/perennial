From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement Require Export Goose.Heap Goose.Filesys.

Inductive Op : Type -> Type :=
| FilesysOp : forall T, FS.Op T -> Op T
| DataOp : forall T, Data.Op T -> Op T.

Instance data_inj : Injectable Data.Op Op := DataOp.
Instance fs_inj : Injectable FS.Op Op := FilesysOp.

(* TODO: wrap up semantics and crash steps into a layer *)
