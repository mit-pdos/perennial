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
Context `{!goGlobalsGS Σ}.
Context `{!syncG Σ}.

#[global]
Program Instance race_pkg_is_init : IsPkgInit race := ltac2:(build_pkg_init ()).

#[global]
Program Instance pkg_is_init : IsPkgInit sync := ltac2:(build_pkg_init ()).

End defns.
