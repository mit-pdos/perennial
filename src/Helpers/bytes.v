From Coq Require Import ZArith.
From Coq Require Import ssreflect.
From Perennial.Helpers Require Import Integers byte_explode List.
From stdpp Require Import base numbers list_numbers.
Open Scope Z.

Open Scope general_if_scope.

Local Open Scope nat.
Lemma nat_off_explode (P: nat → Prop)
  (Bit0: P 0) (Bit1: P 1) (Bit2: P 2) (Bit3: P 3) (Bit4: P 4) (Bit5: P 5) (Bit6: P 6) (Bit7: P 7) :
  ∀ (off: nat),
    off < 8 →
    P off.
Proof.
  intros.
  destruct off; [ assumption |].
  destruct off; [ assumption |].
  destruct off; [ assumption |].
  destruct off; [ assumption |].
  destruct off; [ assumption |].
  destruct off; [ assumption |].
  destruct off; [ assumption |].
  destruct off; [ assumption |].
  lia.
Qed.
Close Scope nat.

Lemma Z_off_explode (P: Z → Prop)
  (Bit0: P 0) (Bit1: P 1) (Bit2: P 2) (Bit3: P 3) (Bit4: P 4) (Bit5: P 5) (Bit6: P 6) (Bit7: P 7) :
  ∀ (off: Z),
    0 ≤ off < 8 →
    P off.
Proof.
  intros.
  replace off with (Z.of_nat (Z.to_nat off)) by lia.
  apply (nat_off_explode (λ x, P (Z.of_nat x))); auto.
  lia.
Qed.

Tactic Notation "bit_off_cases" constr(off) :=
  let t := type of off in
  lazymatch t with
  | nat => pattern off; apply nat_off_explode; [..| try word]
  | Z => pattern off; apply Z_off_explode; [..| try word]
  end.

Tactic Notation "bit_cases" constr(bit) :=
  pattern bit; apply bit_off_explode; [..| done ].

Tactic Notation "byte_cases" constr(b) :=
  pattern b; apply byte_explode.

Ltac vm_refl := vm_compute; reflexivity.

Definition byte_to_bits (x: byte): list bool :=
  Z.testbit (uint.Z x) <$> seqZ 0 8.

Theorem length_byte_to_bits x : length (byte_to_bits x) = 8%nat.
Proof.
  rewrite /byte_to_bits length_fmap length_seqZ //.
Qed.

#[global]
Hint Rewrite length_byte_to_bits : len.

Definition bits_to_byte (bs: list bool): byte :=
   W8 (fold_right Z.add 0 (imap (λ n (b: bool), if b then 2^(Z.of_nat n) else 0) bs)).

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

Definition bytes_to_bits l := mjoin (byte_to_bits <$> l).

Instance bytes_to_bits_inj : Inj (=) (=) bytes_to_bits.
Proof.
  rewrite /bytes_to_bits.
  intros ?? Heq.
  eapply list_join_inj in Heq.
  3: { apply Forall_fmap, Forall_true. naive_solver. }
  3: { apply Forall_fmap, Forall_true. naive_solver. }
  2: lia.
  by apply (inj _) in Heq.
Qed.

Lemma length_bytes_to_bits b :
  length (bytes_to_bits b) = (8 * length b)%nat.
Proof.
  induction b; [done|].
  rewrite /= IHb. lia.
Qed.

#[global] Hint Rewrite length_bytes_to_bits : len.

Lemma bytes_to_bits_app a b :
  bytes_to_bits (a ++ b) = bytes_to_bits a ++ bytes_to_bits b.
Proof. rewrite /bytes_to_bits !fmap_app join_app //. Qed.

Lemma testbit_spec a n :
  0 ≤ n →
  Z.testbit a n = bool_decide (Z.land a (2 ^ n) ≠ 0).
Proof.
  intros. case_bool_decide as Heq.
  - apply Automation.word.decision_assume_opposite.
    intros Ht. apply Heq. clear Heq. rename Ht into Heq.
    apply not_true_is_false in Heq.
    apply Z.bits_inj_iff. intros p.
    rewrite Z.land_spec Z.bits_0.
    destruct (decide (p = n)).
    { subst.
      rewrite Z.pow2_bits_true; [|word].
      by rewrite andb_true_r. }
    rewrite Z.pow2_bits_false; [|word].
    by rewrite andb_false_r.
  - apply (f_equal (λ x, Z.testbit x n)) in Heq.
    rewrite Z.land_spec Z.bits_0 Z.pow2_bits_true in Heq; [|done].
    by rewrite andb_true_r in Heq.
Qed.

Lemma lookup_byte_to_bits byt i :
  (i < 8)%nat →
  byte_to_bits byt !! i =
    Some $ bool_decide (word.and byt (word.slu (W8 1) (W8 (Z.of_nat i))) ≠ W8 0).
Proof.
  intros. rewrite /byte_to_bits.
  assert (∀ x, bool_decide (x ≠ W8 0) = bool_decide (uint.Z x ≠ 0)) as ->.
  { intros. repeat case_bool_decide; word. }
  rewrite word.unsigned_and_nowrap.
  rewrite Automation.word.unsigned_slu'; [|word].
  rewrite left_id.
  replace (uint.Z (W8 (Z.of_nat i))) with (Z.of_nat i) by word.
  rewrite wrap_small.
  2: { split; [lia|]. apply Z.pow_lt_mono_r; word. }

  rewrite list_lookup_fmap.
  rewrite lookup_seqZ_lt; [|lia].
  rewrite left_id /=.
  f_equal.
  rewrite testbit_spec; [done|lia].
Qed.
