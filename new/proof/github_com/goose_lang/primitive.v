From New.proof Require Import proof_prelude.
From New.golang Require Import theory.lock.
Require Import New.code.github_com.goose_lang.primitive.
Require Import New.generatedproof.github_com.goose_lang.primitive.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem_fn : GoSemanticsFunctions} {sem : go.PreSemantics}.
Context {package_sem : primitive.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) primitive := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) primitive := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop primitive get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    primitive.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init primitive }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  iEval (rewrite is_pkg_init_unfold /=).
  by iFrame "∗#".
Qed.

Lemma wp_Assume (cond : bool) :
  {{{ True }}}
    @! primitive.Assume #cond
  {{{ RET #(); ⌜ cond = true ⌝ }}}.
Proof.
  wp_start as "#Hdef".
  destruct cond; wp_auto.
  - wp_end.
  - iLöb as "IH". wp_auto.
    wp_apply ("IH" with "[$]").
Qed.

Lemma wp_Assume_true :
  ∀ Φ,
  Φ #() -∗
  WP @! primitive.Assume #true {{ Φ }}.
Proof.
  iIntros (Φ) "HΦ".
  wp_apply wp_Assume.
  iIntros "%". iFrame.
Qed.

Lemma wp_Assume_false :
  ⊢ ∀ Φ,
  WP @! primitive.Assume #false {{ Φ }}.
Proof.
  iIntros (Φ).
  wp_apply wp_Assume.
  iIntros "%"; congruence.
Qed.

(* FIXME: get rid of this, or document why a lemma for [ⁱᵐᵖˡ] is needed. *)
Lemma wp_RandomUint64__impl :
  {{{ True }}}
    primitive.RandomUint64ⁱᵐᵖˡ #()
  {{{ (x: w64), RET #x; True }}}
.
Proof.
  wp_start as "_".
  wp_apply wp_ArbitraryInt.
  iIntros (x).
  by iApply "HΦ".
Qed.

Lemma wp_RandomUint64 :
  {{{ True }}}
    @! primitive.RandomUint64 #()
  {{{ (x: w64), RET #x; True }}}
.
Proof.
  wp_start_folded as "_".
  wp_func_call.
  by iApply wp_RandomUint64__impl.
Qed.

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

Theorem init_Mutex R E m : m ↦ (zero_val bool) -∗ ▷ R ={E}=∗ is_Mutex m R.
Proof.
  iIntros "H HR".
  simpl.
  iMod (init_lock with "H HR") as "Hm".
  done.
Qed.

Lemma wp_Mutex__Lock m R :
  {{{ is_Mutex m R }}}
    m @! (go.PointerType primitive.Mutex) @! "Lock" #()
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
  {{{ is_Mutex m R ∗ own_Mutex m ∗ ▷ R }}}
    m @! (go.PointerType primitive.Mutex) @! "Unlock" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "(#His & Hlocked & HR)".
  wp_apply (wp_lock_unlock with "[$His $Hlocked $HR]").
  by iApply "HΦ".
Qed.

End wps.
