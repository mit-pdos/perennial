From stdpp Require Import base.
From RecordUpdate Require Import RecordUpdate.
From Tactical Require Import ProofAutomation.

From RecoveryRefinement Require Import Helpers.RelationAlgebra.

From RecoveryRefinement Require Import Spec.Proc.
From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement Require Import Spec.Layer.
From RecoveryRefinement Require Export Goose.Machine Goose.Heap Goose.Filesys.

Inductive Op `{GoModel} : Type -> Type :=
| FilesysOp : forall T, FS.Op T -> Op T
| DataOp : forall T, Data.Op T -> Op T.

Instance data_inj `{GoModel} : Injectable Data.Op Op := DataOp.
Instance fs_inj `{GoModel} : Injectable FS.Op Op := FilesysOp.

Module Go.
  Section GoModel.
  Context `{model_wf:GoModelWf}.
  Notation State := FS.State.

  Inductive step : forall T, Op T -> relation State State T :=
  | StepFilesysOp T (op: FS.Op T) s res :
      FS.step op s res ->
      step (FilesysOp op) s res
  | StepDataOpOk T (op: Data.Op T) s h' v :
      Data.step op (FS.heap s) (Val h' v) ->
      step (DataOp op) s (Val (set FS.heap (fun _ => h') s) v)
  | StepDataOpErr T (op: Data.Op T) s :
      Data.step op (FS.heap s) Err ->
      step (DataOp op) s Err
  .

  Definition sem : Dynamics Op State :=
    {| Proc.step := step;
       Proc.crash_step := FS.crash_step;
       Proc.finish_step := FS.crash_step; |}.

  Definition l : Layer Op.
    refine {| OpState := FS.State;
              Layer.sem := sem;
              trace_proj := fun _ => nil;
              initP := fun s => s = ∅ |};
      simpl; unfold puts;
        propositional.
    - auto.
    - descend; intuition eauto.
    - descend; intuition eauto.
    - apply FS.crash_step_non_err in H; eauto.
    - apply FS.crash_step_non_err in H; eauto.
  Defined.

  End GoModel.
End Go.
