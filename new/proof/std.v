From New.proof Require Import proof_prelude.
From New.code.github_com.goose_lang Require Import std.
From New.proof Require Import machine.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Lemma wp_SumNoOverflow (x y : u64) :
  ∀ Φ : val → iProp Σ,
    Φ #(bool_decide (uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z)) -∗
    WP std.SumNoOverflow #x #y {{ Φ }}.
Proof.
  iIntros (Φ) "HΦ".
  rewrite /SumNoOverflow. wp_pures.
  wp_apply wp_ref_ty; [econstructor|].
  iIntros (y_ptr) "Hy".
  wp_apply wp_ref_ty; [econstructor|].
  iIntros (x_ptr) "Hx".
  wp_pures. wp_load. wp_load. wp_load. wp_pures.
  iModIntro. iExactEq "HΦ".
  repeat f_equal.
  apply bool_decide_ext.
  pose proof (sum_overflow_check x y).
  destruct (decide (uint.Z x ≤ uint.Z (word.add x y))); intuition idtac.
  - word.
  - word.
Qed.

Lemma wp_SumAssumeNoOverflow (x y : u64) :
  ∀ Φ : val → iProp Σ,
    (⌜uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z⌝ -∗ Φ #(LitInt $ word.add x y)) -∗
    WP std.SumAssumeNoOverflow #x #y {{ Φ }}.
Proof.
  iIntros "%Φ HΦ". wp_rec; wp_pures.
  wp_apply wp_ref_ty; [econstructor|].
  iIntros (y_ptr) "Hy".
  wp_apply wp_ref_ty; [econstructor|].
  iIntros (x_ptr) "Hx".
  wp_pures. wp_load. wp_load.
  wp_apply wp_SumNoOverflow.
  wp_apply wp_Assume.
  rewrite bool_decide_eq_true.
  iIntros (?). wp_pures. do 2 wp_load. wp_pures. iModIntro.
  iApply "HΦ". iPureIntro. done.
Qed.
End wps.
