From stdpp Require Import decidable countable.
From coqutil Require Import Datatypes.HList.
From coqutil Require Import Word.Interface.
From coqutil Require Import Word.Naive.
From coqutil Require Import Word.LittleEndian.

Open Scope Z_scope.

Record u64 := U64 { u64_car :> word64 }.
Record u32 := U32 { u32_car :> word32 }.
(* we don't actually do anything with a byte except use its zero value and
encode integers into bytes, so nothing operates on bytes for now. *)
Record byte := U8 { u8_car: word8 }.

Instance naive_word_eq_dec width : EqDecision (word width).
Proof.
  hnf; intros; hnf.
  destruct (decide (unsigned x = unsigned y)); [ left | right ].
  - apply eq_unsigned in e; auto.
  - abstract congruence.
Defined.

Instance u64_eq_dec : EqDecision u64.
Proof. solve_decision. Qed.

Instance u32_eq_dec : EqDecision u32.
Proof. solve_decision. Qed.

Instance byte_eq_dec : EqDecision byte.
Proof. solve_decision. Defined.

Instance word_countable width (H: 0 < width) : Countable (word width).
Proof.
  assert (word.ok (word width)).
  { apply Naive.ok.
    auto. }
  apply (inj_countable'
           word.unsigned
           (fun z => word.of_Z z)); intros.
  by rewrite word.of_Z_unsigned.
Qed.

Lemma unsigned_in_range {width} (x: word width) :
  0 < width ->
  0 <= unsigned x < 2 ^ width.
Proof.
  intros.
  assert (0 < 2^width).
  { assert (2^0 < 2^width).
    { apply Z.pow_lt_mono_r; lia. }
    lia. }
  destruct x; simpl.
  apply Z.mod_small_iff in _unsigned_in_range; intuition lia.
Qed.

Theorem unsigned_mod_bound width (x: word width) :
  unsigned x `mod` 2 ^ width = unsigned x.
Proof.
  destruct x; simpl; auto.
Qed.

Theorem word_unsigned_mod_bound width (x: word width) :
  word.unsigned x `mod` 2 ^ width = word.unsigned x.
Proof.
  simpl.
  rewrite unsigned_mod_bound; auto.
Qed.

Definition width64_ok : 0 < 64 := eq_refl.
Definition width32_ok : 0 < 32 := eq_refl.
Definition width8_ok : 0 < 8 := eq_refl.

Hint Resolve width64_ok width32_ok width8_ok : typeclass_instances.

Instance u64_countable : Countable u64.
Proof.
  apply (inj_countable' u64_car U64); by intros [].
Qed.

Instance u32_countable : Countable u32.
Proof.
  apply (inj_countable' u32_car U32); by intros [].
Qed.

Instance byte_countable : Countable byte.
Proof.
  apply (inj_countable' u8_car U8); by intros [].
Qed.

Module int.
  Class arith (w:Type) :=
    {
      val: w -> Z;
      nat := (fun x => Z.to_nat (val x));
      of_Z: Z -> w;
      add: w -> w -> w;
      eqb: w -> w -> bool;
      ltb: w -> w -> bool;
      leb := fun w1 w2 => ltb w1 w2 || eqb w1 w2;
    }.

  Class arith_ok width {w} (a: arith w) :=
    {
      val_bound : forall x, 0 <= val x < 2 ^ width;
    }.
End int.

Instance u64_arith : int.arith u64 :=
  {|
    int.val := fun (w: u64) => word.unsigned w;
    int.of_Z := fun z => U64 (word.of_Z z);
    int.add := fun w1 w2 => U64 (word.add w1 w2);
    int.eqb := word.eqb;
    int.ltb := word.ltu;
  |}.

Instance u64_arith_ok : int.arith_ok 64 u64_arith.
Proof.
  constructor.
  - intros x.
    pose proof (unsigned_in_range x).
    simpl; lia.
Qed.

Instance u32_arith : int.arith u32 :=
  {|
    int.val := fun (w: u32) => word.unsigned w;
    int.of_Z := fun z => U32 (word.of_Z z);
    int.add := fun w1 w2 => U32 (word.add w1 w2);
    int.eqb := word.eqb;
    int.ltb := word.ltu;
  |}.

Instance u32_arith_ok : int.arith_ok 32 u32_arith.
Proof.
  constructor.
  - intros x.
    pose proof (unsigned_in_range x).
    simpl; lia.
Qed.

Theorem u64_Z_through_nat (x:u64) : Z.of_nat (int.nat x) = int.val x.
Proof.
  unfold int.nat; intros.
  rewrite Z2Nat.id; auto.
  pose proof int.val_bound x; lia.
Qed.

Theorem u64_nat_through_Z (x:u64) : Z.to_nat (int.val x) = int.nat x.
Proof.
  unfold int.nat; intros.
  reflexivity.
Qed.

Definition u64_le (x: u64) : list byte :=
  let n := word.unsigned x.(u64_car) in
  let t := split (byte:=Naive.word8) 8 n in
  let word8s := tuple.to_list t in
  map U8 word8s.

Definition le_to_u64 (l: list byte) : u64.
Proof.
  refine (U64 (word.of_Z _)).
  set (t := tuple.of_list (map u8_car l)).
  exact (combine (byte:=Naive.word8) _ t).
Defined.

Theorem u64_le_length x : length (u64_le x) = 8%nat.
Proof.
  reflexivity.
Qed.

Theorem tuple_to_list_length A n (t: tuple A n) :
  length (tuple.to_list t) = n.
Proof.
  induction n; simpl; auto.
Qed.

Theorem tuple_of_to_list8 A (t: tuple A 8) :
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
  intros [x]; simpl.
  unfold le_to_u64, u64_le.
  f_equal.
  cbv [u64_car].
  rewrite map_map, map_id.
  rewrite tuple_of_to_list8.
  rewrite combine_split.
  change (8%nat * 8) with 64.
  rewrite word_unsigned_mod_bound by lia.
  by rewrite word.of_Z_unsigned.
Qed.
