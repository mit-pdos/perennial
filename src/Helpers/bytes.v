From Coq Require Import ZArith.
From Coq Require Import ssreflect.
From Perennial.Helpers Require Import Integers byte_explode.
From stdpp Require Import base numbers list_numbers.
Open Scope Z.

Open Scope general_if_scope.

Tactic Notation "bit_cases" constr(bit) :=
  pattern bit; apply bit_off_explode; [..| done ].

Tactic Notation "byte_cases" constr(b) :=
  pattern b; apply byte_explode.

Ltac vm_refl := vm_compute; reflexivity.

Definition byte_to_bits (x: byte): list bool :=
  Z.testbit (int.Z x) <$> seqZ 0 8.

Theorem length_byte_to_bits x : length (byte_to_bits x) = 8%nat.
Proof.
  rewrite /byte_to_bits fmap_length seqZ_length //.
Qed.

Hint Rewrite length_byte_to_bits : len.

Definition bits_to_byte (bs: list bool): byte :=
   U8 (fold_right Z.add 0 (imap (λ n (b: bool), if b then 2^(Z.of_nat n) else 0) bs)).

Theorem byte_to_bits_to_byte (x:byte) :
  bits_to_byte (byte_to_bits x) = x.
Proof. byte_cases x; vm_refl. Qed.

Lemma explode_bits (bs: list bool) :
  length bs = 8%nat →
  ∃ (b0 b1 b2 b3 b4 b5 b6 b7: bool),
    bs = [b0;b1;b2;b3;b4;b5;b6;b7].
Proof.
  intros Hlen.
  repeat (let b := fresh "b" in
          destruct bs as [|b bs];
          [ simpl in Hlen; lia
          | exists b]).
  destruct bs; [reflexivity | simpl in Hlen; lia].
Qed.

Theorem bits_to_byte_to_bits (bs:list bool) :
  length bs = 8%nat →
  byte_to_bits (bits_to_byte bs) = bs.
Proof.
  intros Hlen.
  apply explode_bits in Hlen as (b0&b1&b2&b3&b4&b5&b6&b7&->).
  (repeat match goal with b:bool |- _ => destruct b end); vm_refl.
Qed.

Global Instance byte_to_bits_inj : Inj eq eq byte_to_bits.
Proof.
  intros b1 b2 Heq%(f_equal bits_to_byte).
  rewrite !byte_to_bits_to_byte // in Heq.
Qed.

Theorem bits_to_byte_inj bs1 bs2 :
  length bs1 = 8%nat →
  length bs2 = 8%nat →
  bits_to_byte bs1 = bits_to_byte bs2 →
  bs1 = bs2.
Proof.
  intros ?? Heq%(f_equal byte_to_bits).
  rewrite !bits_to_byte_to_bits // in Heq.
Qed.

Theorem byte_bit_ext_eq b1 b2 :
  (∀ (off:nat), (off < 8)%nat →
                byte_to_bits b1 !! off = byte_to_bits b2 !! off) →
  b1 = b2.
Proof.
  intros.
  apply (inj byte_to_bits).
  apply (list_eq_same_length _ _ 8); [rewrite length_byte_to_bits // .. | ].
  intros off x1 x2 Hbound.
  intros.
  rewrite H // in H0.
  congruence.
Qed.
