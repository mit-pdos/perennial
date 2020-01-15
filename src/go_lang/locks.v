From Perennial.go_lang Require Import lang notation lib.spin_lock.
From Perennial.go_lang Require Import lifting.
From iris.program_logic Require Import weakestpre.
From Perennial.go_lang Require Import proofmode.
From Perennial.go_lang Require Import typing.
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

  (* a cond var is modeled with the underlying lock *)
  Definition newCond: val := λ: "l", "l".
  (* no-op in the model, only affects scheduling *)
  Definition condSignal: val := λ: "l", #().
  Definition condBroadcast: val := λ: "l", #().
  Definition condWait: val := λ: "l", release "l";;
                                      (* actual cond var waits for a signal
                                      here, but the model does not take this
                                      into account *)
                                      acquire "l".

  Theorem wp_newCond N γ lk R :
    {{{ is_lock N γ lk R }}}
      newCond lk
      {{{ RET lk; is_lock N γ lk R }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    wp_call.
    iApply "HΦ".
    iFrame.
  Qed.

  Theorem wp_condSignal N γ lk R :
    {{{ is_lock N γ lk R }}}
      condSignal lk
      {{{ RET #(); is_lock N γ lk R }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_call.
    iApply ("HΦ" with "[$]").
  Qed.

  Theorem wp_condBroadcast N γ lk R :
    {{{ is_lock N γ lk R }}}
      condBroadcast lk
      {{{ RET #(); is_lock N γ lk R }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_call.
    iApply ("HΦ" with "[$]").
  Qed.

  Theorem wp_condWait N γ lk R :
    {{{ is_lock N γ lk R ∗ spin_lock.locked γ ∗ R }}}
      condWait lk
      {{{ RET #(); is_lock N γ lk R ∗ spin_lock.locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "(#Hc&Hlocked&HR) HΦ".
    wp_call.
    wp_apply (release_spec with "[$Hc $Hlocked $HR]").
    iIntros "_".
    wp_pures.
    wp_apply (acquire_spec with "[$Hc]").
    iIntros "(Hlocked&HR)".
    iApply ("HΦ" with "[$]").
  Qed.

  End go_lang.
End lock.
