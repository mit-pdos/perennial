From New.proof.sync_proof Require Import base.
From New.golang.theory Require Import lock.
Local Existing Instances tokG wg_totalG rw_ghost_varG rw_ghost_wlG rw_ghost_rwmutexG  wg_auth_inG.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : sync.Assumptions}.
Local Set Default Proof Using "All".
Context `{!syncG Σ}.

(** This means [m] is a valid mutex with invariant [R]. *)
Definition is_Mutex (m: loc) (R : iProp Σ) : iProp Σ :=
  is_lock m R.
#[global] Opaque is_Mutex.
#[local] Transparent is_Mutex.

(** This resource denotes ownership of the fact that the Mutex is currently
    locked. *)
Definition own_Mutex (m: loc) : iProp Σ := own_lock m.
#[global] Opaque own_Mutex.
#[local] Transparent own_Mutex.

Lemma own_Mutex_exclusive (m : loc) : own_Mutex m -∗ own_Mutex m -∗ False.
Proof.
  iIntros "H1 H2".
  by iDestruct (own_lock_exclusive with "H1 H2") as %?.
Qed.

Global Instance is_Mutex_ne m : NonExpansive (is_Mutex m).
Proof. solve_proper. Qed.

(** The main proofs. *)
Global Instance is_Mutex_persistent m R : Persistent (is_Mutex m R).
Proof. apply _. Qed.
Global Instance locked_timeless m : Timeless (own_Mutex m).
Proof. apply _. Qed.

Theorem init_Mutex R E m : m ↦ (zero_val sync.Mutex.t) -∗ ▷ R ={E}=∗ is_Mutex m R.
Proof.
  iIntros "Hl HR".
  iMod (init_lock with "Hl HR") as "Hm".
  done.
Qed.

Lemma wp_Mutex__TryLock m R :
  {{{ is_pkg_init sync ∗ is_Mutex m R }}}
    m @! (go.PointerType sync.Mutex) @! "TryLock" #()
  {{{ (locked : bool), RET #locked; if locked then own_Mutex m ∗ R else True }}}.
Proof.
  wp_start as "#His".
  wp_apply (wp_lock_trylock with "[$His]").
  iIntros (locked) "H".
  iApply "HΦ".
  done.
Qed.

Lemma wp_Mutex__Lock m R :
  {{{ is_pkg_init sync ∗ is_Mutex m R }}}
    m @! (go.PointerType sync.Mutex) @! "Lock" #()
  {{{ RET #(); own_Mutex m ∗ R }}}.
Proof.
  wp_start as "#His".
  wp_apply (wp_lock_lock with "[$His]").
  iIntros "[Hown HR]".
  iApply "HΦ".
  iFrame.
Qed.

(* this form is useful for defer statements *)
Lemma wp_Mutex__Unlock m R :
  {{{ is_pkg_init sync ∗ is_Mutex m R ∗ own_Mutex m ∗ ▷ R }}}
    m @! (go.PointerType sync.Mutex) @! "Unlock" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "(#His & Hlocked & HR)".
  wp_apply (wp_lock_unlock with "[$His $Hlocked $HR]").
  by iApply "HΦ".
Qed.

Definition is_Locker (i : interface.t_ok) (P : iProp Σ) : iProp Σ :=
  "#H_Lock" ∷ ({{{ True }}} #(methods i.(interface.ty) "Lock" i.(interface.v)) #() {{{ RET #(); P }}}) ∗
  "#H_Unlock" ∷ ({{{ P }}} #(methods i.(interface.ty) "Unlock" i.(interface.v)) #() {{{ RET #(); True }}}).

Global Instance is_Locker_persistent v P : Persistent (is_Locker v P) := _.

Lemma Mutex_is_Locker (m : loc) R :
  is_pkg_init sync -∗
  is_Mutex m R -∗
  is_Locker (interface.mk (go.PointerType sync.Mutex) #m) (own_Mutex m ∗ R).
Proof.
  iIntros "#? #?".
  iSplitL.
  - iIntros (?) "!# _ HΦ". simpl.
    by wp_apply (wp_Mutex__Lock with "[$]").
  - iIntros (?) "!# [? ?] HΦ". simpl.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "#∗". }
    by iApply "HΦ".
Qed.

End wps.
