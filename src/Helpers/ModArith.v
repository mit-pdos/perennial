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
  int.Z (word.add x y) < int.Z x <-> int.Z x + int.Z y >= 2^64.
Proof.
  split; intros.
  - revert H; word_cleanup; intros.
    rewrite /word.wrap in H1.
    destruct (decide (int.Z x + int.Z y >= 2^64)); [ auto | exfalso ].
    lia.
  - word_cleanup.
    rewrite /word.wrap.
    lia.
Qed.

Lemma sum_nooverflow_l (x y : u64) :
  int.Z x < int.Z (word.add x y) →
  int.Z (word.add x y) = (int.Z x) + (int.Z y).
Proof.
  intros. word_cleanup. rewrite wrap_small //.
  split; first word.
  destruct (Z_lt_ge_dec (int.Z x + int.Z y) (2 ^ 64)) as [Hlt|Hge]; first done.
  apply sum_overflow_check in Hge.
  lia.
Qed.

Lemma word_add_comm (x y : u64) :
  word.add x y = word.add y x.
Proof.
  specialize (@word.ring_theory _ u64_instance.u64 _). intros W.
  rewrite W.(Radd_comm). done.
Qed.

Lemma sum_nooverflow_r (x y : u64) :
  int.Z y < int.Z (word.add x y) →
  int.Z (word.add x y) = (int.Z x) + (int.Z y).
Proof.
  rewrite word_add_comm. intros ?%sum_nooverflow_l.
  rewrite Z.add_comm //.
Qed.

Theorem word_add1_neq (x: u64) :
  int.Z x ≠ int.Z (word.add x (U64 1)).
Proof.
  simpl.
  destruct (decide (int.Z x + 1 < 2^64)%Z); [ word | ].
  rewrite word.unsigned_add.
  change (int.Z (U64 1)) with 1%Z.
  rewrite /word.wrap.
  lia.
Qed.

(* avoid leaving it at div_mod_to_equations since it causes some backwards
incompatibility *)
Ltac Zify.zify_post_hook ::= idtac.
