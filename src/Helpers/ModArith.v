From Coq Require Import ZArith.
From Coq Require Import ssreflect.
From stdpp Require Import base numbers.
From Perennial.Helpers Require Import Integers.

Open Scope Z_scope.
Set Default Goal Selector "!".
Set Default Proof Using "Type".

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma mod_add_modulus a k :
  k ≠ 0 ->
  a `mod` k = (a + k) `mod` k.
Proof.
  intros.
  rewrite -> Z.add_mod by auto.
  rewrite -> Z.mod_same by auto.
  rewrite Z.add_0_r.
  rewrite -> Z.mod_mod by auto.
  auto.
Qed.

Lemma mod_sub_modulus a k :
  k ≠ 0 ->
  a `mod` k = (a - k) `mod` k.
Proof.
  intros.
  rewrite -> Zminus_mod by auto.
  rewrite -> Z.mod_same by auto.
  rewrite Z.sub_0_r.
  rewrite -> Z.mod_mod by auto.
  auto.
Qed.

Theorem sum_overflow_check (x y: u64) :
  int.val (word.add x y) < int.val x <-> int.val x + int.val y >= 2^64.
Proof.
  split; intros.
  - revert H; word_cleanup; intros.
    rewrite /word.wrap in H1.
    destruct (decide (int.val x + int.val y >= 2^64)); [ auto | exfalso ].
    lia.
  - word_cleanup.
    rewrite /word.wrap.
    lia.
Qed.

Theorem word_add1_neq (x: u64) :
  int.val x ≠ int.val (word.add x (U64 1)).
Proof.
  simpl.
  destruct (decide (int.val x + 1 < 2^64)%Z); [ word | ].
  rewrite word.unsigned_add.
  change (int.val (U64 1)) with 1%Z.
  rewrite /word.wrap.
  lia.
Qed.

(* avoid leaving it at div_mod_to_equations since it causes some backwards
incompatibility *)
Ltac Zify.zify_post_hook ::= idtac.
