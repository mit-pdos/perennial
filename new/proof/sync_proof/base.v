Require Export New.code.sync.
From New.proof Require Export proof_prelude.
Require Export New.generatedproof.sync.

From New.proof Require Export sync.atomic.
From New.proof Require Export tok_set.

From New.experiments Require Export glob.
From Perennial Require Export base.

Set Default Proof Using "Type".

Inductive rwmutex := RLocked (num_readers : nat) | Locked.

Inductive wlock_state :=
| NotLocked (unnotified_readers : w32)
| SignalingReaders (remaining_readers : w32)
| WaitingForReaders
| IsLocked.

Class syncG Σ := {
    #[global] tokG :: tok_setG Σ;
    #[global] wg_totalG :: ghost_varG Σ w32;

    #[global] rw_ghost_varG :: ghost_varG Σ ();
    #[global] rw_ghost_wlG :: ghost_varG Σ wlock_state;
    #[global] rw_ghost_rwmutexG :: ghost_varG Σ rwmutex;
  }.

Definition syncΣ := #[tok_setΣ; ghost_varΣ w32; ghost_varΣ (); ghost_varΣ wlock_state; ghost_varΣ rwmutex].
Global Instance subG_syncΣ{Σ} : subG (syncΣ) Σ → (syncG Σ).
Proof. solve_inG. Qed.

Section defns.
Context `{heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!syncG Σ}.

Local Definition race_deps : iProp Σ := ltac2:(build_pkg_init_deps 'race).
#[global] Program Instance : IsPkgInit race :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := race_deps;
  |}.

Local Notation deps := (ltac2:(build_pkg_init_deps 'sync) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit sync :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Notation "'build_get_is_pkg_init'" := (ltac2:(build_get_is_pkg_init_wf ())).

#[global] Instance g : GetIsPkgInitWfDef race := build_get_is_pkg_init.
#[global] Instance g2 : GetIsPkgInitWfDef sync := build_get_is_pkg_init.
Print g2.


End defns.
