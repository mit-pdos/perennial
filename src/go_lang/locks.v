From Perennial.go_lang Require Import lang notation lib.spin_lock.
From Perennial.go_lang Require Import lifting.
From iris.program_logic Require Import weakestpre.
From Perennial.go_lang Require Import proofmode.
From Perennial.go_lang Require Import typing.
From Perennial.go_lang Require Import basic_triples.
Import uPred.

Definition lockRefT {ext} {ext_ty: ext_types ext} := refT boolT.
Definition condvarRefT {ext} {ext_ty: ext_types ext} := refT lockRefT.

Module lock.
  Section go_lang.
  Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ} `{!lockG Σ}.

  Local Coercion Var' (s:string) : expr := Var s.

  Definition new := spin_lock.newlock.
  Definition acquire := spin_lock.acquire.
  Definition release := spin_lock.release.

  (* a cond var (a Go *sync.Cond) is modeled as a pointer to the underlying
  lock *)
  Definition newCond: val := λ: "l", ref "l".
  (* no-op in the model, only affects scheduling *)
  Definition condSignal: val := λ: "l", #().
  Definition condBroadcast: val := λ: "l", #().
  Definition condWait: val := λ: "l", release !"l";;
                                      (* actual cond var waits for a signal
                                      here, but the model does not take this
                                      into account *)
                                      acquire !"l".

  Definition is_cond N γ (c: loc) R: iProp Σ :=
    ∃ lk, c ↦ Free lk ∗ is_lock N γ lk R.

  Theorem wp_newCond N γ lk R :
    {{{ is_lock N γ lk R }}}
      newCond lk
      {{{ c, RET #c; is_cond N γ c R }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    wp_call.
    wp_alloc c as "Hc".
    iApply "HΦ".
    iExists _; iFrame.
  Qed.

  Theorem wp_condSignal N γ c R :
    {{{ is_cond N γ c R }}}
      condSignal #c
      {{{ RET #(); is_cond N γ c R }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_call.
    iApply ("HΦ" with "[$]").
  Qed.

  Theorem wp_condBroadcast N γ c R :
    {{{ is_cond N γ c R }}}
      condBroadcast #c
      {{{ RET #(); is_cond N γ c R }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_call.
    iApply ("HΦ" with "[$]").
  Qed.

  Theorem wp_condWait N γ c R :
    {{{ is_cond N γ c R ∗ spin_lock.locked γ ∗ R }}}
      condWait #c
      {{{ RET #(); is_cond N γ c R ∗ spin_lock.locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "(Hc&Hlocked&HR) HΦ".
    iDestruct "Hc" as (lk) "(Hcptr&#Hc)".
    wp_call.
    wp_load.
    wp_apply (release_spec with "[$Hc $Hlocked $HR]").
    iIntros "_".
    wp_pures.
    wp_load.
    wp_apply (acquire_spec with "[$Hc]").
    iIntros "(Hlocked&HR)".
    iApply "HΦ".
    iSplitR "Hlocked HR"; last by iFrame.
    iExists lk; iFrame "#∗".
  Qed.

  End go_lang.
End lock.
