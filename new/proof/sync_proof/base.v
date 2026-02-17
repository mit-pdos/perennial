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

Module sync.
Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : sync.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) sync := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) sync := build_get_is_pkg_init_wf.

Definition is_initialized : iProp Σ :=
  ∃ (p: loc),
    global_addr sync.expunged ↦□ p ∗
    p ↦□ interface.nil.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop sync get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    sync.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init sync }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  wp_apply wp_GlobalAlloc as "expunged".
  wp_apply (synctest.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (race.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (atomic.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }

  wp_alloc expunged_p as "Hexpunged_p".
  iPersist "Hexpunged_p".
  wp_auto.

  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

End wps.
End sync.
