From stdpp Require Import base.
From RecordUpdate Require Import RecordUpdate.
From Tactical Require Import ProofAutomation.

From RecoveryRefinement Require Import Helpers.RelationAlgebra.
From RecoveryRefinement Require Import Helpers.RecordZoom.

From RecoveryRefinement Require Import Spec.Proc.
From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement Require Import Spec.Layer.
From RecoveryRefinement.Goose Require Export Machine Heap Filesys Globals.

Inductive Op `{GoModel} : Type -> Type :=
| FilesysOp : forall T, FS.Op T -> Op T
| DataOp : forall T, Data.Op T -> Op T
| LockGlobalOp : forall T, Globals.Op (slice.t LockRef) T -> Op T
.

Instance data_inj `{GoModel} : Injectable Data.Op Op := DataOp.
Instance fs_inj `{GoModel} : Injectable FS.Op Op := FilesysOp.
Instance lock_global_inj `{GoModel} : Injectable (Globals.Op (slice.t LockRef)) Op := LockGlobalOp.

Module Go.
  Section GoModel.
  Context `{model_wf:GoModelWf}.
  Record State : Type :=
    { fs: FS.State;
      maillocks: Globals.State (slice.t LockRef); }.

  Global Instance etaState : Settable _ := settable! Build_State <fs; maillocks>.

  Definition step T (op:Op T) : relation State State T :=
    match op with
    | FilesysOp op => _zoom fs (FS.step op)
    | DataOp op => _zoom fs (_zoom FS.heap (Data.step op))
    | LockGlobalOp op => _zoom maillocks (Globals.step op)
    end.

  Import RelationNotations.

  Definition crash_step : relation State State unit :=
    _zoom fs FS.crash_step;;
          _zoom maillocks (puts (fun _ => Globals.init)).

  Theorem crash_step_non_err : forall s res,
      crash_step s res -> res <> Err.
  Proof.
    unfold crash_step, and_then, puts; intros.
    destruct res; cbn [_zoom zoom] in *; eauto.
    intuition eauto.
    - apply FS.crash_step_non_err in H1; congruence.
    - propositional; congruence.
  Qed.

  Definition sem : Dynamics Op State :=
    {| Proc.step := step;
       Proc.crash_step := crash_step;
       Proc.finish_step := crash_step; |}.

  Ltac t :=
    repeat match goal with
           | |- exists (_:State), _ => eexists (Build_State _ _)
           | |- exists _, _ => eexists
           | _ => progress propositional
           | |- _ /\ _ => split
           | |- _ => solve [ eauto ]
           end.

  Definition l : Layer Op.
    refine {| OpState := State;
              Layer.sem := sem;
              trace_proj := fun _ => nil;
              initP := fun s => s = ∅ |};
      simpl; unfold puts, pure;
        propositional.
    - auto.
    - t.
    - t.
    - apply crash_step_non_err in H; auto.
    - apply crash_step_non_err in H; auto.
  Defined.

  End GoModel.
End Go.
