From stdpp Require Import base.
From RecordUpdate Require Import RecordUpdate.
From Tactical Require Import ProofAutomation.

From RecoveryRefinement Require Import Helpers.RelationAlgebra.
From RecoveryRefinement Require Import Helpers.RecordZoom.

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

  Definition step T (op:Op T) : relation State State T :=
    match op with
    | FilesysOp op => FS.step op
    | DataOp op => _zoom FS.heap (Data.step op)
    end.

  Definition sem : Dynamics Op State :=
    {| Proc.step := step;
       Proc.crash_step := FS.crash_step;
       Proc.finish_step := FS.crash_step; |}.

  Definition l : Layer Op.
    refine {| OpState := FS.State;
              Layer.sem := sem;
              trace_proj := fun _ => nil;
              initP := fun s => s = ∅ |};
      simpl; unfold puts, pure;
        propositional.
    - auto.
    - descend; intuition eauto.
      descend; intuition eauto.
    - descend; intuition eauto.
      descend; intuition eauto.
    - apply FS.crash_step_non_err in H; eauto.
    - apply FS.crash_step_non_err in H; eauto.
  Defined.

  End GoModel.
End Go.
