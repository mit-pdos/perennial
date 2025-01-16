From New.proof Require Import proof_prelude.
From New.code.github_com.goose_lang Require std.
From New.proof Require Import machine.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Lemma wp_SumNoOverflow (x y : u64) :
  {{{ True }}}
    func_call #std.pkg_name' #"SumNoOverflow" #x #y
  {{{ RET #(bool_decide (uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z)); True }}}.
Proof.
  iIntros (Φ) "#Hdef HΦ".
  wp_bind (func_call _ _).
  unshelve wp_apply (wp_func_call with "[]"); [| | tc_solve | | ]; try iFrame "#".
  wp_func_call.
  rewrite /SumNoOverflow. wp_pures.
  wp_alloc y_ptr as "Hy".
  wp_pures.
  wp_alloc x_ptr as "Hx".
  wp_pures. wp_load. wp_load. wp_load. wp_pures.
  iExactEq "HΦ".
  repeat f_equal.
  apply bool_decide_ext.
  pose proof (sum_overflow_check x y).
  destruct (decide (uint.Z x ≤ uint.Z (word.add x y))); intuition idtac.
  - word.
  - word.
Qed.

Lemma wp_SumAssumeNoOverflow (x y : u64) :
  ∀ Φ : val → iProp Σ,
    (⌜uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z⌝ -∗ Φ #(word.add x y)) -∗
    WP std.SumAssumeNoOverflow #x #y {{ Φ }}.
Proof.
  iIntros "%Φ HΦ". wp_call.
  wp_alloc y_ptr as "Hy".
  wp_pures.
  wp_alloc x_ptr as "Hx".
  wp_pures. wp_load. wp_pures. wp_load.
  wp_pures. wp_apply wp_SumNoOverflow.
  wp_pures.
  wp_apply wp_Assume.
  rewrite bool_decide_eq_true.
  iIntros (?). wp_pures. do 2 wp_load. wp_pures.
  iApply "HΦ". iPureIntro. done.
Qed.
End wps.
