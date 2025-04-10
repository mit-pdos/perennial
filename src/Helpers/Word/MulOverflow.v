From Coq Require Import ZArith.
From stdpp Require Import base numbers.
From Perennial.Helpers.Word Require Import Integers Automation.

Open Scope Z_scope.

Lemma mul_overflow_check_conservative (x y: w64) :
  0 < uint.Z x →
  (2 ^ 64 - 1) `div` uint.Z y >= uint.Z x →
  uint.Z x * uint.Z y < 2^64.
Proof.
  intros Hz1 n1.
  apply Z.ge_le_iff in n1.
  assert (uint.Z x * uint.Z y ≤ 2^64-1); [ | word ].
  apply (Z.mul_le_mono_pos_r _ _ (uint.Z y)) in n1; [ | word ].
  word.
Qed.

Lemma mul_overflow_check_correct (x y: w64) :
  uint.Z x ≠ 0 →
  uint.Z y ≠ 0 →
  2 ^ 64 - 1 < uint.Z x * uint.Z y ↔ (2 ^ 64 - 1) `div` uint.Z y < uint.Z x.
Proof.
  intros Hnz1 Hnz2.
  set (u64_max := 2^64-1).
  split.
  - subst u64_max.
    pose proof (mul_overflow_check_conservative x y).
    word.
  - intros H.
    assert (u64_max `div` uint.Z y + 1 ≤ uint.Z x) by lia.
    apply (Z.mul_le_mono_nonneg_r _ _ (uint.Z y)) in H0; [ | word ].
    rewrite Z.mul_add_distr_r in H0.
    replace (u64_max `div` uint.Z y * uint.Z y) with (u64_max - u64_max `mod` uint.Z y) in H0 by word.
    word.
Qed.
