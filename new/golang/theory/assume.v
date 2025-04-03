From New Require Export notation.
From New.golang.defn Require Export builtin assume.
From New.golang.theory Require Export typing proofmode.
From Perennial Require Import base.

Set Default Proof Using "Type".

Section wps.

Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Lemma wp_assume (b: bool) Φ :
  (⌜b = true⌝ -∗ Φ #()) -∗
  WP assume #b {{ Φ }}.
Proof.
  iIntros "HΦ".
  wp_call.
  destruct b; wp_pures.
  - iApply "HΦ"; auto.
  - iClear "∗".
    iLöb as "IH".
    wp_pure.
    iApply "IH".
Qed.

Lemma wp_assume_sum_no_overflow (x y: w64) Φ :
  (⌜uint.Z x + uint.Z y < 2^64⌝ -∗ Φ #()) -∗
  WP assume_sum_no_overflow #x #y {{ Φ }}.
Proof.
  iIntros "HΦ".
  wp_call.
  wp_apply wp_assume.
  iIntros (H).
  apply bool_decide_eq_true in H.
  wp_pures.
  iApply "HΦ".
  iPureIntro.
  move: H; word.
Qed.

Lemma wp_sum_assume_no_overflow (x y: w64) Φ :
  (⌜uint.Z x + uint.Z y < 2^64⌝ -∗ Φ #(word.add x y)) -∗
  WP sum_assume_no_overflow #x #y {{ Φ }}.
Proof.
  iIntros "HΦ".
  wp_call.
  wp_apply wp_assume_sum_no_overflow.
  iIntros (H).
  wp_pures.
  iApply "HΦ".
  auto.
Qed.

End wps.
