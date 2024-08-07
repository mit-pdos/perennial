From iris.proofmode Require Import proofmode.
From Perennial.Helpers Require Import Integers.

Lemma uint_nat_W64 (n : nat) :
  n < 2 ^ 64 ->
  uint.nat (W64 n) = n.
Proof. intros H. word. Qed.

Lemma uint_nat_word_add_S (x : u64) :
  uint.Z x < 2 ^ 64 - 1 ->
  (uint.nat (w64_word_instance.(word.add) x (W64 1))) = S (uint.nat x).
Proof. intros H. word. Qed.
