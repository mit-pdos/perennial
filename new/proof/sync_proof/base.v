Require Export New.code.sync.
From New.proof Require Export proof_prelude.
Require Export New.generatedproof.sync.

From New.proof Require Export sync.atomic internal.race internal.synctest.
From New.proof Require Export tok_set.
From Perennial.algebra Require Export auth_prop.

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
<<<<<<< HEAD
    #[global] tokG :: tok_setG Σ;
    #[global] semaG :: ghost_varG Σ w32;
    #[global] wg_totalG :: ghost_varG Σ Z;
=======
    #[local] tokG :: tok_setG Σ;
    #[local] wg_totalG :: ghost_varG Σ w32;
>>>>>>> master

    #[local] rw_ghost_varG :: ghost_varG Σ ();
    #[local] rw_ghost_wlG :: ghost_varG Σ wlock_state;
    #[local] rw_ghost_rwmutexG :: ghost_varG Σ rwmutex;

    #[local] wg_auth_inG :: auth_propG Σ;
  }.
Local Existing Instances tokG wg_totalG rw_ghost_varG rw_ghost_wlG wg_auth_inG.

<<<<<<< HEAD
Definition syncΣ := #[tok_setΣ; ghost_varΣ w32; ghost_varΣ Z; ghost_varΣ (); ghost_varΣ wlock_state; ghost_varΣ rwmutex].
=======
Definition syncΣ := #[tok_setΣ; ghost_varΣ w32; ghost_varΣ (); ghost_varΣ wlock_state; ghost_varΣ rwmutex; auth_propΣ].
>>>>>>> master
Global Instance subG_syncΣ{Σ} : subG (syncΣ) Σ → (syncG Σ).
Proof. solve_inG. Qed.

Section defns.
Context `{heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!syncG Σ}.

#[global] Instance : IsPkgInit sync := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf sync := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop sync get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init ∗ is_go_context ∗ □ is_pkg_defined sync }}}
    sync.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init sync }}}.
Proof.
  intros Hinit. wp_start as "(Hown & #? & #Hdef)".
  wp_call. wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  wp_apply (synctest.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  { iModIntro. iEval simpl_is_pkg_defined in "Hdef". iPkgInit. }
  wp_apply (race.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  { iModIntro. iEval simpl_is_pkg_defined in "Hdef". iPkgInit. }
  wp_apply (atomic.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  { iModIntro. iEval simpl_is_pkg_defined in "Hdef". iPkgInit. }
  wp_call. iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#".  done.
Qed.

End defns.
