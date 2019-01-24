From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Database.Filesys.
From RecoveryRefinement Require Import Database.DataStructures.

From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement Require Import Helpers.RelationAlgebra.
From RecordUpdate Require Import RecordSet.
Import ApplicativeNotations.

Inductive Op : Type -> Type :=
| FilesysOp : forall T, FS.Op T -> Op T
| DataOp : forall T, Data.Op T -> Op T.

Instance data_inj : Injectable Data.Op Op := DataOp.
Instance fs_inj : Injectable FS.Op Op := FilesysOp.

Module Layer.

  Record State :=
    mkState { fsΣ : FS.State;
              dataΣ : Data.State; }.

  Instance eta : Settable _ := mkSettable (constructor mkState <*> fsΣ <*> dataΣ)%set.

  Inductive step T : Op T -> relation State State T :=
  | FilesysOpErr : forall op s,
      FS.step op s.(fsΣ) Err ->
      step (FilesysOp op) s Err
  | FilesysOpStep : forall op s s' r,
      FS.step op s.(fsΣ) (Val s' r) ->
      step (FilesysOp op) s (Val (set fsΣ (fun _ => s') s) r)
  | DataOpErr : forall op s,
      Data.step op s.(dataΣ) Err ->
      step (DataOp op) s Err
  | DataOpStep : forall op s s' r,
      Data.step op s.(dataΣ) (Val s' r) ->
      step (DataOp op) s (Val (set dataΣ (fun _ => s') s) r)
  .

End Layer.
