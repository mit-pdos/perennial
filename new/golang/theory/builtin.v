From New Require Export notation.
From New.golang.defn Require Export builtin.
From New.golang.theory Require Import typing proofmode.
From Perennial Require Import base.

Set Default Proof Using "Type".

Module error.
  Section def.
  Context `{ffi_syntax}.
  Definition t := interface.t.
  End def.
End error.

Section wps.

Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance wp_int64_ge0 (x : w64) : PureWp True (int_ge0 #x) #(bool_decide (0 ≤ sint.Z x)).
Proof.
  pure_wp_start.
  iExactEq "HΦ".
  repeat f_equal.
  apply bool_decide_ext.
  word.
Qed.

(* NOTE: turned out to be unused *)
Lemma swrap_neg (l: w64) :
  sint.Z l < 0 →
  word.swrap (word:=w64_word_instance) (uint.Z l) = uint.Z l - 2^64.
Proof.
  intros Hneg.
  rewrite swrap_large; try word.
Qed.

Global Instance wp_int64_lt (l r : w64) : PureWp True (int_lt #l #r) #(bool_decide (sint.Z l < sint.Z r)).
Proof.
  pure_wp_start.
  destruct (bool_decide_reflect (0 ≤ sint.Z l)%Z); wp_pures.
  - destruct (bool_decide_reflect (0 ≤ sint.Z r)%Z); wp_pures.
    + iExactEq "HΦ"; repeat f_equal; apply bool_decide_ext.
      word.
    + rewrite bool_decide_eq_false_2 //. word.
  - destruct (bool_decide_reflect (0 ≤ sint.Z r)%Z); wp_pures.
    + rewrite bool_decide_eq_true_2 //. word.
    + iExactEq "HΦ"; repeat f_equal; apply bool_decide_ext.
      word.
Qed.

Global Instance wp_int64_gt (l r : w64) : PureWp True (int_gt #l #r) #(bool_decide (sint.Z l > sint.Z r)).
Proof.
  pure_wp_start.
  iExactEq "HΦ"; repeat f_equal; apply bool_decide_ext.
  word.
Qed.

Global Instance wp_int32_gt (l r : w32) : PureWp True (int_gt #l #r) #(bool_decide (sint.Z l > sint.Z r)).
Proof. Admitted.

Global Instance wp_int32_lt (l r : w32) : PureWp True (int_lt #l #r) #(bool_decide (sint.Z l < sint.Z r)).
Proof. Admitted.

Global Instance wp_int64_leq (l r : w64) : PureWp True (int_leq #l #r) #(bool_decide (sint.Z l ≤ sint.Z r)).
Proof.
  pure_wp_start.
  destruct (bool_decide_reflect (l = r)); wp_pures.
  - rewrite bool_decide_eq_true_2 //. word.
  - iExactEq "HΦ"; repeat f_equal; apply bool_decide_ext.
    word.
Qed.

Global Instance wp_int64_geq (l r : w64) : PureWp True (int_geq #l #r) #(bool_decide (sint.Z l >= sint.Z r)).
Proof.
  pure_wp_start.
  iExactEq "HΦ"; repeat f_equal; apply bool_decide_ext.
  word.
Qed.

Global Instance wp_int32_geq (l r : w32) : PureWp True (int_geq #l #r) #(bool_decide (sint.Z l >= sint.Z r)).
Proof. Admitted.

Global Instance wp_int32_leq (l r : w32) : PureWp True (int_leq #l #r) #(bool_decide (sint.Z l ≤ sint.Z r)).
Proof. Admitted.

End wps.

#[global] Opaque int_lt int_leq int_gt int_geq.
