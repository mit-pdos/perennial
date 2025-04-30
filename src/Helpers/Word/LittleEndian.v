From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From Perennial Require Import base.
From coqutil Require Import Datatypes.HList.
From coqutil.Word Require Import Interface Properties.
From Perennial.Helpers.Word Require Import Integers Properties.
(* imported last to ensure split and combine refer to this library *)
From Perennial Require Import Helpers.LittleEndian.

(* these make sure that s/64/32/ changes 64-bit code to 32-bit code *)
Notation w64_bytes := 8%nat (only parsing).
Notation w32_bytes := 4%nat (only parsing).

Definition u64_le_def (x: u64) : list byte :=
  let n := word.unsigned x in
  let t := split (byte:=w8_word_instance) w64_bytes n in
  tuple.to_list t.
Program Definition u64_le := sealed @u64_le_def.
Definition u64_le_unseal : u64_le = _ := seal_eq _.

Definition u32_le_def (x: u32) : list byte :=
  let n := word.unsigned x in
  let t := split (byte:=w8_word_instance) w32_bytes n in
  tuple.to_list t.
Program Definition u32_le := sealed @u32_le_def.
Definition u32_le_unseal : u32_le = _ := seal_eq _.

Local Ltac unseal := rewrite ?u64_le_unseal ?u32_le_unseal.

(** 64-bit encoding *)

Definition le_to_u64 (l: list byte) : u64.
Proof.
  refine (word.of_Z _).
  set (t := tuple.of_list l).
  exact (combine (byte:=w8_word_instance) _ t).
Defined.

Lemma u64_le_0 : u64_le (W64 0) = replicate w64_bytes (W8 0).
Proof. unseal. reflexivity. Qed.

Theorem u64_le_length x : length (u64_le x) = w64_bytes.
Proof. unseal. reflexivity. Qed.

Theorem tuple_of_to_list_u64 {A} (t: tuple A w64_bytes) :
  tuple.of_list (tuple.to_list t) = t.
Proof.
  unfold tuple in t.
  repeat match goal with
         | [ t: hlist _ |- _ ] => destruct t
         end.
  f_equal.
Qed.

Theorem u64_le_to_word : forall x,
    le_to_u64 (u64_le x) = x.
Proof.
  unseal.
  intros x; simpl.
  unfold le_to_u64, u64_le_def.
  rewrite -> tuple_of_to_list_u64.
  rewrite combine_split.
  change (Z.of_nat w64_bytes * 8) with 64.
  rewrite word.wrap_unsigned.
  rewrite word.of_Z_unsigned.
  done.
Qed.

(* end 64-bit code *)

(** 32-bit encoding *)

Definition le_to_u32 (l: list byte) : u32.
Proof.
  refine (word.of_Z _).
  set (t := tuple.of_list l).
  exact (combine (byte:=w8_word_instance) _ t).
Defined.

Lemma u32_le_0 : u32_le (W32 0) = replicate w32_bytes (W8 0).
Proof. unseal. reflexivity. Qed.

Theorem u32_le_length x : length (u32_le x) = w32_bytes.
Proof. unseal. reflexivity. Qed.

Theorem tuple_of_to_list_u32 {A} (t: tuple A w32_bytes) :
  tuple.of_list (tuple.to_list t) = t.
Proof.
  unfold tuple in t.
  repeat match goal with
         | [ t: hlist _ |- _ ] => destruct t
         end.
  f_equal.
Qed.

Theorem u32_le_to_word : forall x,
    le_to_u32 (u32_le x) = x.
Proof.
  unseal.
  intros x; simpl.
  unfold le_to_u32, u32_le_def.
  rewrite -> tuple_of_to_list_u32.
  rewrite combine_split.
  change (Z.of_nat w32_bytes * 8) with 32.
  rewrite word.wrap_unsigned.
  rewrite word.of_Z_unsigned.
  done.
Qed.

(* end 32-bit code *)

Global Instance u64_le_inj : Inj (=) (=) u64_le.
Proof.
  intros x y H%(f_equal le_to_u64).
  rewrite !u64_le_to_word in H. auto.
Qed.

Global Instance u32_le_inj : Inj (=) (=) u32_le.
Proof.
  intros x y H%(f_equal le_to_u32).
  rewrite !u32_le_to_word in H. auto.
Qed.

Lemma combine_unfold n b (t: HList.tuple byte n) :
  combine (S n) {| PrimitivePair.pair._1 := b; PrimitivePair.pair._2 := t |} =
  Z.lor (uint.Z b) (combine n t ≪ 8).
Proof. reflexivity. Qed.

Theorem Zmod_small_bits_high p z n :
  0 <= z < 2 ^ p ->
  0 <= p <= n ->
  Z.testbit z n = false.
Proof.
  intros.
  rewrite <- (Z.mod_small z (2^p)) by lia.
  rewrite Z.mod_pow2_bits_high; auto; lia.
Qed.

Theorem combine_bound n t :
  0 <= combine n t < 2 ^ (8 * Z.of_nat n).
Proof.
  induction n; simpl.
  - cbv; split; congruence.
  - destruct t as [b t].
    let T := type of t in change T with (HList.tuple byte n) in *.
    rewrite combine_unfold.
    rewrite BitOps.or_to_plus.
    { pose proof (IHn t).
      pose proof (word.unsigned_range b).
      split.
      { unfold Z.shiftl; simpl. lia. }
      { unfold Z.shiftl; simpl.
        replace (2 ^ (8 * Z.of_nat (S n))) with (2^8 * 2 ^ (8 * Z.of_nat n)); try lia.
        replace (8 * Z.of_nat (S n)) with (8 + 8*Z.of_nat n) by lia.
        rewrite <- Z.pow_add_r; lia. } }
    pose proof (word.unsigned_range b).
    apply Z.bits_inj.
    unfold Z.eqf; intros.
    rewrite Z.land_spec.
    rewrite Z.bits_0.
    destruct (decide (n0 < 0)).
    { rewrite Z.testbit_neg_r; [ | lia ].
      rewrite andb_false_l; auto.
    }
    destruct (decide (n0 < 8)).
    + rewrite Z.shiftl_spec_low; [ | lia ].
      rewrite andb_false_r; auto.
    + rewrite (Zmod_small_bits_high 8); [ | lia | lia ].
      rewrite andb_false_l; auto.
Qed.


Lemma le_to_u64_le bs :
  length bs = 8%nat ->
  u64_le (le_to_u64 bs) = bs.
Proof.
  unseal.
  intros.
  do 8 (destruct bs; [ simpl in H; lia | ]).
  destruct bs; [ clear H | simpl in H; lia ].
  unfold le_to_u64, u64_le_def.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small.
  { rewrite LittleEndian.split_combine.
    simpl; auto. }
  cbv [length].
  apply combine_bound.
Qed.
