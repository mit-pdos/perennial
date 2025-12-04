From New.proof.sync_proof Require Import base.
From New.golang.theory Require Import lock.
Local Existing Instances tokG wg_totalG rw_ghost_varG rw_ghost_wlG rw_ghost_rwmutexG  wg_auth_inG.

Section proof.
Context `{heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!syncG Σ}.

(** This means [m] is a valid mutex with invariant [R]. *)
Definition is_Mutex (m: loc) (R : iProp Σ) : iProp Σ :=
  is_lock (struct.field_ref_f sync.Mutex "state" m) R.
#[global] Opaque is_Mutex.
#[local] Transparent is_Mutex.

(** This resource denotes ownership of the fact that the Mutex is currently
    locked. *)
Definition own_Mutex (m: loc) : iProp Σ := own_lock (struct.field_ref_f sync.Mutex "state" m).
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

Theorem init_Mutex R E m : m ↦ (default_val Mutex.t) -∗ ▷ R ={E}=∗ is_Mutex m R.
Proof.
  iIntros "Hl HR".
  simpl.
  iDestruct (struct_fields_split with "Hl") as "Hl".
  iNamed "Hl". simpl.
  iMod (init_lock with "Hstate HR") as "Hm".
  done.
Qed.

Lemma wp_Mutex__TryLock m R :
  {{{ is_pkg_init sync ∗ is_Mutex m R }}}
    m @ (ptrT.id sync.Mutex.id) @ "TryLock" #()
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
    m @ (ptrT.id sync.Mutex.id) @ "Lock" #()
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
    m @ (ptrT.id sync.Mutex.id) @ "Unlock" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "(#His & Hlocked & HR)".
  wp_apply (wp_lock_unlock with "[$His $Hlocked $HR]").
  by iApply "HΦ".
Qed.

Definition is_Locker (i : interface.t) (P : iProp Σ) : iProp Σ :=
  "#H_Lock" ∷ ({{{ True }}} (interface.get #"Lock" #i) #() {{{ RET #(); P }}}) ∗
  "#H_Unlock" ∷ ({{{ P }}} (interface.get #"Unlock" #i) #() {{{ RET #(); True }}}).

Global Instance is_Locker_persistent v P : Persistent (is_Locker v P) := _.

Lemma Mutex_is_Locker (m : loc) R :
  is_pkg_init sync -∗
  is_Mutex m R -∗
  is_Locker (interface.mk (ptrT.id sync.Mutex.id) #m) (own_Mutex m ∗ R).
Proof.
  iIntros "#? #?".
  iSplitL.
  - iIntros (?) "!# _ HΦ".
    wp_auto.
    by wp_apply (wp_Mutex__Lock with "[$]").
  - iIntros (?) "!# [? ?] HΦ".
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "#∗". }
    by iApply "HΦ".
Qed.

End proof.
