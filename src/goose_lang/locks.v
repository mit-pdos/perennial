From Perennial.goose_lang Require Import lang notation lib.spin_lock.
From Perennial.goose_lang Require Import lifting.
From iris.program_logic Require Import weakestpre.
From Perennial.goose_lang Require Import proofmode.
From Perennial.goose_lang Require Import readonly.
From Perennial.goose_lang Require Import typing.
From Perennial.goose_lang Require Import basic_triples.
Import uPred.

Definition lockRefT {ext} {ext_ty: ext_types ext} := refT boolT.
Definition condvarRefT {ext} {ext_ty: ext_types ext} := refT lockRefT.

Module lock.
  Section goose_lang.
  Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ} `{!lockG Σ}.
  Context {ext_tys: ext_types ext}.

  Local Coercion Var' (s:string) : expr := Var s.

  Definition new := spin_lock.newlock.
  Definition acquire := spin_lock.acquire.
  Definition release := spin_lock.release.

  Theorem new_free_lock stk E :
    {{{ True }}}
      new #() @ stk; E
    {{{ l, RET #l; is_free_lock l }}}.
  Proof.
    iIntros (l) "_ HΦ".
    wp_call.
    wp_apply wp_alloc; [ eauto | ].
    iIntros (l') "Hl".
    iApply ("HΦ" with "[$]").
  Qed.

  Theorem is_free_lock_ty lk :
    is_free_lock lk -∗ ⌜val_ty #lk lockRefT⌝.
  Proof.
    iIntros "Hlk".
    iPureIntro.
    val_ty.
  Qed.

  Theorem is_lock_ty N γ lk R :
    is_lock N γ lk R -∗ ⌜val_ty lk lockRefT⌝.
  Proof.
    iIntros "Hlk".
    iDestruct (is_lock_flat with "Hlk") as (l) "->".
    iPureIntro.
    val_ty.
  Qed.

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
    ∃ lk, c ↦ro lk ∗ is_lock N γ lk R.

  Theorem is_cond_dup N γ c R :
    is_cond N γ c R -∗ is_cond N γ c R ∗ is_cond N γ c R.
  Proof.
    iIntros "Hc".
    iDestruct "Hc" as (lk) "[[Hc1 Hc2] #Hl]".
    iSplitL "Hc1"; iExists lk; iFrame "#∗".
  Qed.

  Theorem wp_newCond N γ lk R :
    {{{ is_lock N γ lk R }}}
      newCond lk
    {{{ c, RET #c; is_cond N γ c R }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    wp_call.
    iDestruct (is_lock_flat with "Hl") as %[l ->].
    wp_apply wp_alloc_untyped; [ auto | ].
    iIntros (c) "Hc".
    rewrite ptsto_ro_weaken.
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
    iDestruct (ptsto_ro_load with "Hcptr") as (q) "Hcptr".
    wp_load.
    wp_apply (release_spec with "[$Hc $Hlocked $HR]").
    wp_pures.
    wp_load.
    wp_apply (acquire_spec with "[$Hc]").
    iIntros "(Hlocked&HR)".
    iApply "HΦ".
    iSplitR "Hlocked HR"; last by iFrame.
    iExists lk; iFrame "#∗".
    iApply (ptsto_ro_from_q with "[$]").
  Qed.

  End goose_lang.
End lock.
