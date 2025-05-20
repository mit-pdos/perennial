From New Require Export notation.
From New.golang.defn Require Export builtin assume.
From New.golang.theory Require Export typing proofmode.
From Perennial Require Import base.

Set Default Proof Using "Type".

Section wps.

Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Lemma wp_assume (b: bool) stk E Φ :
  (⌜b = true⌝ -∗ Φ #()) -∗
  WP assume #b @ stk; E {{ Φ }}.
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

Lemma wp_assume_sum_no_overflow (x y: w64) stk E Φ :
  (⌜uint.Z x + uint.Z y < 2^64⌝ -∗ Φ #()) -∗
  WP assume_sum_no_overflow #x #y @ stk; E {{ Φ }}.
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

Lemma wp_sum_assume_no_overflow (x y: w64) stk E Φ :
  (⌜uint.Z x + uint.Z y < 2^64⌝ -∗ Φ #(word.add x y)) -∗
  WP sum_assume_no_overflow #x #y @ stk; E {{ Φ }}.
Proof.
  iIntros "HΦ".
  wp_call.
  wp_apply wp_assume_sum_no_overflow.
  iIntros (H).
  wp_pures.
  iApply "HΦ".
  auto.
Qed.

Lemma wp_mul_overflows (x y: w64) stk E Φ :
  (Φ #(bool_decide (2^64 ≤ uint.Z x * uint.Z y))) -∗
  WP mul_overflows #x #y @ stk; E {{ Φ }}.
Proof.
  iIntros "HΦ".
  wp_call.
  destruct (decide (uint.Z x = 0)).
  {
    rewrite (bool_decide_eq_true_2 (x = _)); [ | word ].
    wp_pures.
    rewrite bool_decide_eq_false_2; [ | word ]. done.
  }
  rewrite (bool_decide_eq_false_2 (x = _)); [ | word ].
  wp_pures.
  destruct (decide (uint.Z y = 0)).
  {
    rewrite (bool_decide_eq_true_2 (y = _)); [ | word ].
    wp_pures.
    rewrite bool_decide_eq_false_2; [ | word ]. done.
  }
  rewrite (bool_decide_eq_false_2 (y = _)); [ | word ].
  wp_pures.
  iExactEq "HΦ".
  repeat f_equal.
  apply bool_decide_ext.
  rewrite word.unsigned_divu_nowrap; [ | word ].
  change (uint.Z (W64 (2^64-1))) with (2^64-1).
  pose proof (mul_overflow_check_correct x y ltac:(word)).
  word.
Qed.

Lemma wp_assume_mul_no_overflow (x y: w64) stk E Φ :
  (⌜uint.Z x * uint.Z y < 2^64⌝ → Φ #()) -∗
  WP assume_mul_no_overflow #x #y @ stk; E {{ Φ }}.
Proof.
  iIntros "HΦ".
  wp_call.
  wp_apply wp_mul_overflows.
  wp_pures.
  wp_apply wp_assume.
  match goal with
  | |- context[bool_decide ?P] => destruct (bool_decide_reflect P)
  end.
  { iIntros (?); congruence. }
  iIntros (_). iApply "HΦ".
  iPureIntro. lia.
Qed.

End wps.
