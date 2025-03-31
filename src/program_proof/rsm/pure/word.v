From iris.proofmode Require Import proofmode.
From Perennial.Helpers Require Import Integers.

Lemma uint_nat_W64_0 :
  uint.Z (W64 0) = O.
Proof. word. Qed.

Lemma uint_nat_W64_of_nat (n : nat) :
  n < 2 ^ 64 ->
  uint.Z (W64 n) = n.
Proof. intros H. word. Qed.

Lemma uint_nat_word_add_S (x : u64) :
  uint.Z x < 2 ^ 64 - 1 ->
  (uint.Z (word.add x (W64 1))) = Z.succ (uint.Z x).
Proof. intros H. word. Qed.

Lemma uint_nat_u64_inj (x y : u64) :
  uint.Z x = uint.Z y ->
  x = y.
Proof. intros H. word. Qed.
