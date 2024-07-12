From stdpp Require Import decidable countable finite.
From coqutil Require Import Datatypes.HList.
From coqutil.Z Require Import BitOps.
From coqutil.Word Require Naive.
From coqutil.Word Require Export Interface Properties.
From Perennial Require Import Helpers.LittleEndian.

Open Scope Z_scope.

#[global]
Instance word_inhabited width (word: Interface.word width) : Inhabited word.
Proof.
  constructor.
  exact (word.of_Z 0).
Qed.

Definition shift_overflow_special_case_handlers := {|
  Naive.div_by_zero x := -1;
  Naive.mod_by_zero x := x;
  (* returns a new shift amount, which we leave as too large (so that the
  overall shift always produces 0) *)
  Naive.adjust_too_big_shift_amount n := n;
|}.

Notation word64 := (Naive.gen_word 64%Z shift_overflow_special_case_handlers).
#[global] Instance word64_ok : word.ok word64 := Naive.gen_ok 64 _ eq_refl.
Notation word32 := (Naive.gen_word 32%Z shift_overflow_special_case_handlers).
#[global] Instance word32_ok : word.ok word32 := Naive.gen_ok 32 _ eq_refl.
Notation word8 := (Naive.gen_word 8%Z shift_overflow_special_case_handlers).
#[global] Instance word8_ok : word.ok word8 := Naive.gen_ok 8 _ eq_refl.

Record w64_rep := Word64 { w64_car : word64 }.
Record w32_rep := Word32 { w32_car : word32 }.
Record w8_rep := Word8 { w8_car : word8 }.

Definition width64_ok : 0 < 64 := eq_refl.
Definition width32_ok : 0 < 32 := eq_refl.
Definition width8_ok : 0 < 8 := eq_refl.

#[global]
Hint Resolve width64_ok width32_ok width8_ok : typeclass_instances.

Opaque Naive.word.


Module w64_instance.
  Import Interface.word.
  Notation "'lift1' f" := (fun w => Word64 (f w.(w64_car))) (at level 10, only parsing).
  Notation "'lift2' f" := (fun w1 w2 => Word64 (f w1.(w64_car) w2.(w64_car))) (at level 10, only parsing).
  #[global]
  Instance w64 : word 64 :=
    {|
      rep := w64_rep;
      unsigned w := unsigned w.(w64_car);
      signed w := signed (w.(w64_car));
      of_Z z := Word64 (of_Z z);
      add := lift2 add;
      sub := lift2 sub;
      opp := lift1 opp;
      or := lift2 or;
      and := lift2 and;
      xor := lift2 xor;
      not := lift1 not;
      ndn := lift2 ndn;
      mul := lift2 mul;
      mulhss := lift2 mulhss;
      mulhsu := lift2 mulhsu;
      mulhuu := lift2 mulhuu;
      divu := lift2 divu;
      divs := lift2 divs;
      modu := lift2 modu;
      mods := lift2 mods;
      slu := lift2 slu;
      sru := lift2 sru;
      srs := lift2 srs;
      eqb w1 w2 := eqb w1.(w64_car) w2.(w64_car);
      ltu w1 w2 := ltu w1.(w64_car) w2.(w64_car);
      lts w1 w2 := lts w1.(w64_car) w2.(w64_car);
      sextend width' := lift1 (sextend width');
    |}.

  Global Instance w64_word_ok : word.ok w64.
  Proof.
    destruct word64_ok.
    constructor; intros; eauto; try solve [ simpl in *; subst wrap0; eauto ].
    simpl.
    destruct x as [x]; f_equal; simpl.
    rewrite <- of_Z_unsigned0; auto.
  Qed.

End w64_instance.

Module w32_instance.
  Import Interface.word.
  Notation "'lift1' f" := (fun w => Word32 (f w.(w32_car))) (at level 10, only parsing).
  Notation "'lift2' f" := (fun w1 w2 => Word32 (f w1.(w32_car) w2.(w32_car))) (at level 10, only parsing).
  #[global]
  Instance w32 : word 32 :=
    {|
      rep := w32_rep;
      unsigned w := unsigned w.(w32_car);
      signed w := signed (w.(w32_car));
      of_Z z := Word32 (of_Z z);
      add := lift2 add;
      sub := lift2 sub;
      opp := lift1 opp;
      or := lift2 or;
      and := lift2 and;
      xor := lift2 xor;
      not := lift1 not;
      ndn := lift2 ndn;
      mul := lift2 mul;
      mulhss := lift2 mulhss;
      mulhsu := lift2 mulhsu;
      mulhuu := lift2 mulhuu;
      divu := lift2 divu;
      divs := lift2 divs;
      modu := lift2 modu;
      mods := lift2 mods;
      slu := lift2 slu;
      sru := lift2 sru;
      srs := lift2 srs;
      eqb w1 w2 := eqb w1.(w32_car) w2.(w32_car);
      ltu w1 w2 := ltu w1.(w32_car) w2.(w32_car);
      lts w1 w2 := lts w1.(w32_car) w2.(w32_car);
      sextend width' := lift1 (sextend width');
    |}.

  Global Instance w32_word_ok : word.ok w32.
  Proof.
    destruct word32_ok.
    constructor; intros; eauto; try solve [ simpl in *; subst wrap0; eauto ].
    simpl.
    destruct x as [x]; f_equal; simpl.
    rewrite <- of_Z_unsigned0; auto.
  Qed.

End w32_instance.

Module w8_instance.
  Import Interface.word.
  Notation "'lift1' f" := (fun w => Word8 (f w.(w8_car))) (at level 10, only parsing).
  Notation "'lift2' f" := (fun w1 w2 => Word8 (f w1.(w8_car) w2.(w8_car))) (at level 10, only parsing).
  #[global]
  Instance w8 : word 8 :=
    {|
      rep := w8_rep;
      unsigned w := unsigned w.(w8_car);
      signed w := signed (w.(w8_car));
      of_Z z := Word8 (of_Z z);
      add := lift2 add;
      sub := lift2 sub;
      opp := lift1 opp;
      or := lift2 or;
      and := lift2 and;
      xor := lift2 xor;
      not := lift1 not;
      ndn := lift2 ndn;
      mul := lift2 mul;
      mulhss := lift2 mulhss;
      mulhsu := lift2 mulhsu;
      mulhuu := lift2 mulhuu;
      divu := lift2 divu;
      divs := lift2 divs;
      modu := lift2 modu;
      mods := lift2 mods;
      slu := lift2 slu;
      sru := lift2 sru;
      srs := lift2 srs;
      eqb w1 w2 := eqb w1.(w8_car) w2.(w8_car);
      ltu w1 w2 := ltu w1.(w8_car) w2.(w8_car);
      lts w1 w2 := lts w1.(w8_car) w2.(w8_car);
      sextend width' := lift1 (sextend width');
    |}.

  Global Instance w8_word_ok : word.ok w8.
  Proof.
    destruct word8_ok.
    constructor; intros; eauto; try solve [ simpl in *; subst wrap0; eauto ].
    simpl.
    destruct x as [x]; f_equal; simpl.
    rewrite <- of_Z_unsigned0; auto.
  Qed.

End w8_instance.

Global Opaque w64_instance.w64 w32_instance.w32 w8_instance.w8.

(* these are identity coercions to make notation.v work out (this is still black
magic to me) *)

Global SubClass w64 := @word.rep _ w64_instance.w64.
Global SubClass w32 := @word.rep _ w32_instance.w32.
Global SubClass w8 := @word.rep _ w8_instance.w8.

(* "Add Ring" special options are black magic from coqutil.
  Sometimes, it'll fail with "Cannot find a declared ring structure over "w64""
  or "Goal is not an equation (of expected equality) eq".
  To fix this, do "unfold w64 in *; ring; fold w64 in *".
  TODO: for some reason, unfolding doesn't work as a preprocess step.
*)
Add Ring w64_ring : (word.ring_theory (word := w64_instance.w64))
  (preprocess [autorewrite with rew_word_morphism],
   morphism (word.ring_morph (word := w64_instance.w64)),
   constants [Properties.word_cst]).

Add Ring w32_ring : (word.ring_theory (word := w32_instance.w32))
  (preprocess [autorewrite with rew_word_morphism],
   morphism (word.ring_morph (word := w32_instance.w32)),
   constants [Properties.word_cst]).

Add Ring w8_ring : (word.ring_theory (word := w8_instance.w8))
  (preprocess [autorewrite with rew_word_morphism],
   morphism (word.ring_morph (word := w8_instance.w8)),
   constants [Properties.word_cst]).

(* TODO: ideally this is rarely or never used, but it's useful for backwards
compatibility while we're still experimenting *)
Notation byte := w8 (only parsing).

Definition W64 (x:Z) : w64 := word.of_Z x.
Definition W32 (x:Z) : w32 := word.of_Z x.
Definition W8 (x:Z)  : w8  := word.of_Z x.

(* Compatibility for existing code that refers to U64, u64, etc *)
Notation U64 x := (W64 x) (only parsing).
Notation U32 x := (W32 x) (only parsing).
Notation U8 x := (W8 x) (only parsing).
Notation u64 := w64 (only parsing).
Notation u32 := w32 (only parsing).
Notation u8 := w8 (only parsing).

#[global]
Instance word_eq_dec {width} (word: word width) {word_ok: word.ok word} : EqDecision word.
Proof.
  hnf; intros; hnf.
  pose proof (word.eqb_spec x y).
  destruct (word.eqb x y);
    [ left | right]; inversion H; auto.
Defined.

#[global]
Instance w64_eq_dec : EqDecision w64 := _.
#[global]
Instance w32_eq_dec : EqDecision w32 := _.
#[global]
Instance w8_eq_dec : EqDecision w8 := _.

#[global]
Instance int_Z_inj `(word: Interface.word width) {word_ok: word.ok word} : Inj eq eq (@word.unsigned width _).
Proof.
  intros x1 x2.
  intros.
  apply word.unsigned_inj in H; auto.
Qed.

#[global]
Instance sint_Z_inj `(word: Interface.word width) {word_ok: word.ok word} : Inj eq eq (@word.signed width _).
Proof.
  intros x1 x2.
  intros.
  apply word.signed_inj in H; auto.
Qed.

#[global]
Instance byte_eq_dec : EqDecision byte.
Proof. solve_decision. Defined.

#[global]
Instance word_countable `(word: Interface.word width) {word_ok: word.ok word} : Countable word.
Proof.
  apply (inj_countable'
           word.unsigned
           (fun z => word.of_Z z)); intros.
  by rewrite word.of_Z_unsigned.
Qed.

#[global]
Instance w64_countable : Countable w64.
Proof. apply _. Qed.
#[global]
Instance w32_countable : Countable w32.
Proof. apply _. Qed.
#[global]
Instance w8_countable : Countable byte.
Proof. apply _. Qed.

(* uint and the u64_through* theorems are for backwards compatibility *)
(* Note[SB]: it's a bit long to write `Z.to_nat (word.unsigned x)`,
so maybe still keep some notation for this? *)

Module uint.
  Notation Z := word.unsigned.

  Notation nat x := (Z.to_nat (Z x)).
End uint.

Module sint.
  Notation Z := word.signed.
End sint.

Theorem u64_Z_through_nat (x:w64) : Z.of_nat (uint.nat x) = uint.Z x.
Proof.
  rewrite Z2Nat.id; auto.
  pose proof (word.unsigned_range x); lia.
Qed.

(* should maybe convert this into an explicit match on ints at some point *)
Definition u8_to_ascii (x:byte) : Ascii.ascii := Ascii.ascii_of_nat (uint.nat x).

(* conversion to string *)
Definition u8_to_string (x:byte) : String.string := String.String (u8_to_ascii x) String.EmptyString.

Theorem wrap_small `{word: Interface.word width} {ok: word.ok word} (x:Z) :
  0 <= x < 2^width ->
  word.wrap x = x.
Proof.
  unfold word.wrap; intros.
  rewrite Zmod_small; auto.
Qed.

Theorem swrap_small `{word: Interface.word width} {ok: word.ok word} (x:Z) :
  width > 0 ->
  -(2^(width-1)) <= x < 2^(width-1) ->
  @word.swrap _ word x = x.
Proof.
  unfold word.swrap; intros.
  unshelve epose proof ZLib.Z.pow2_times2 width _; first by lia.
  rewrite Zmod_small; lia.
Qed.

Theorem u8_to_u64_Z (x:w8) : uint.Z (W64 (uint.Z x)) = uint.Z x.
Proof.
  unfold W64.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small; auto.
  pose proof (word.unsigned_range x); lia.
Qed.

Theorem u32_to_u64_Z (x:w32) : uint.Z (W64 (uint.Z x)) = uint.Z x.
Proof.
  unfold W64.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small; auto.
  pose proof (word.unsigned_range x); lia.
Qed.

Theorem u32_from_u64_Z (x: u64) : uint.Z x < 2^32 ->
                                  uint.Z (W32 (uint.Z x)) = uint.Z x.
Proof.
  unfold W32; intros.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small; auto.
  pose proof (word.unsigned_range x); lia.
Qed.

Theorem s8_to_s64_Z (x:w8) : sint.Z (W64 (sint.Z x)) = sint.Z x.
Proof.
  unfold W64.
  rewrite word.signed_of_Z.
  rewrite swrap_small; auto; first by lia.
  pose proof (word.signed_range x); lia.
Qed.

Theorem s32_to_s64_Z (x:w32) : sint.Z (W64 (sint.Z x)) = sint.Z x.
Proof.
  unfold W64.
  rewrite word.signed_of_Z.
  rewrite swrap_small; auto; first by lia.
  pose proof (word.signed_range x); lia.
Qed.

Theorem s32_from_s64_Z (x: w64) : -2^(32-1) ≤ sint.Z x < 2^(32-1) ->
                                  sint.Z (W32 (sint.Z x)) = sint.Z x.
Proof.
  unfold W32; intros.
  rewrite word.signed_of_Z.
  rewrite swrap_small; auto; first by lia.
Qed.

Theorem tuple_to_list_length A n (t: tuple A n) :
  length (tuple.to_list t) = n.
Proof.
  induction n; simpl; auto.
Qed.

(* these make sure that s/64/32/ changes 64-bit code to 32-bit code *)
Notation w64_bytes := 8%nat (only parsing).
Notation w32_bytes := 4%nat (only parsing).

(** 64-bit encoding *)
Definition u64_le (x: u64) : list byte :=
  let n := word.unsigned x in
  let t := split (byte:=w8_instance.w8) w64_bytes n in
  tuple.to_list t.
Global Arguments u64_le : simpl never.

Definition le_to_u64 (l: list byte) : u64.
Proof.
  refine (word.of_Z _).
  set (t := tuple.of_list l).
  exact (combine (byte:=w8_instance.w8) _ t).
Defined.

Lemma u64_le_0 : u64_le (W64 0) = replicate w64_bytes (W8 0).
Proof. reflexivity. Qed.

Theorem u64_le_length x : length (u64_le x) = w64_bytes.
Proof.
  reflexivity.
Qed.

Theorem tuple_of_to_list_u64 A (t: tuple A w64_bytes) :
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
  intros x; simpl.
  unfold le_to_u64, u64_le.
  f_equal.
  rewrite tuple_of_to_list_u64.
  rewrite combine_split.
  change (Z.of_nat w64_bytes * 8) with 64.
  rewrite word.wrap_unsigned by lia.
  by rewrite word.of_Z_unsigned.
Qed.
(* end 64-bit code *)

(* this block is a copy-paste of the above with s/64/32/ *)
(** 32-bit encoding *)
Definition u32_le (x: u32) : list byte :=
  let n := word.unsigned x in
  let t := split (byte:=w8_instance.w8) w32_bytes n in
  tuple.to_list t.
Global Arguments u32_le : simpl never.

Definition le_to_u32 (l: list byte) : u32.
Proof.
  refine (word.of_Z _).
  set (t := tuple.of_list l).
  exact (combine (byte:=w8_instance.w8) _ t).
Defined.

Lemma u32_le_0 : u32_le (W32 0) = replicate w32_bytes (W8 0).
Proof. reflexivity. Qed.

Theorem u32_le_length x : length (u32_le x) = w32_bytes.
Proof.
  reflexivity.
Qed.

Theorem tuple_of_to_list_u32 A (t: tuple A w32_bytes) :
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
  intros x; simpl.
  unfold le_to_u32, u32_le.
  f_equal.
  rewrite tuple_of_to_list_u32.
  rewrite combine_split.
  change (Z.of_nat w32_bytes * 8) with 32.
  rewrite word.wrap_unsigned by lia.
  by rewrite word.of_Z_unsigned.
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
Proof.
  reflexivity.
Qed.

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
  intros.
  do 8 (destruct bs; [ simpl in H; lia | ]).
  destruct bs; [ clear H | simpl in H; lia ].
  unfold u64_le, le_to_u64.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small.
  { rewrite LittleEndian.split_combine.
    simpl; auto. }
  cbv [length].
  match goal with
  | |- context[LittleEndian.combine ?n ?t] =>
    pose proof (combine_bound n t)
  end.
  exact H.
Qed.

Lemma unsigned_U64 z : uint.Z (W64 z) = word.wrap (word:=w64_instance.w64) z.
Proof.
  unfold W64; rewrite word.unsigned_of_Z; auto.
Qed.

Lemma unsigned_U32 z : uint.Z (W32 z) = word.wrap (word:=w32_instance.w32) z.
Proof.
  unfold W32; rewrite word.unsigned_of_Z; auto.
Qed.

Lemma unsigned_U64_0 : uint.Z (W64 0) = 0.
Proof.
  reflexivity.
Qed.

Lemma unsigned_U32_0 : uint.Z (W32 0) = 0.
Proof.
  reflexivity.
Qed.

Lemma signed_U64 z : sint.Z (W64 z) = word.swrap (word:=w64_instance.w64) z.
Proof.
  unfold W64; rewrite word.signed_of_Z; auto.
Qed.

Lemma signed_U32 z : sint.Z (W32 z) = word.swrap (word:=w32_instance.w32) z.
Proof.
  unfold W32; rewrite word.signed_of_Z; auto.
Qed.

Lemma signed_U64_0 : sint.Z (W64 0) = 0.
Proof.
  reflexivity.
Qed.

Lemma signed_U32_0 : sint.Z (W32 0) = 0.
Proof.
  reflexivity.
Qed.

Create HintDb word.

Ltac word_cleanup :=
  repeat autounfold with word in *;
  try match goal with
      | |- @eq u64 _ _ => apply word.unsigned_inj
      | |- @eq u32 _ _ => apply word.unsigned_inj
      | |- @eq u8 _ _ => apply word.unsigned_inj
      end;
  (* can't replace this with [autorewrite], probably because typeclass inference
  isn't the same *)
  rewrite ?word.unsigned_add, ?word.unsigned_sub,
  ?word.unsigned_divu_nowrap, ?word.unsigned_modu_nowrap,
  ?unsigned_U64_0, ?unsigned_U32_0,
  ?word.unsigned_of_Z, ?word.of_Z_unsigned, ?unsigned_U64, ?unsigned_U32;
  try autorewrite with word;
  repeat match goal with
         | [ H: context[word.unsigned (W64 (Zpos ?x))] |- _ ] => change (uint.Z (Zpos x)) with (Zpos x) in *
         | [ |- context[word.unsigned (W64 (Zpos ?x))] ] => change (uint.Z (Zpos x)) with (Zpos x)
         | [ H: context[word.unsigned (W32 (Zpos ?x))] |- _ ] => change (uint.Z (W32 (Zpos x))) with (Zpos x) in *
         | [ |- context[word.unsigned (W32 (Zpos ?x))] ] => change (uint.Z (W32 (Zpos x))) with (Zpos x)
         end;
  repeat match goal with
         | [ |- context[uint.Z ?x] ] =>
           lazymatch goal with
           | [ H': 0 <= uint.Z x < 2^_ |- _ ] => fail
           | [ H': 0 <= uint.Z x <= 2^_ |- _ ] => fail (* TODO: should be unnecessary *)
           | _ => pose proof (word.unsigned_range x)
           end
         | [ H: context[uint.Z ?x] |- _ ] =>
           lazymatch goal with
           | [ H': 0 <= uint.Z x < 2^_ |- _ ] => fail
           | [ H': 0 <= uint.Z x <= 2^_ |- _ ] => fail (* TODO: should be unnecessary *)
           | _ => pose proof (word.unsigned_range x)
           end
         end;
  repeat match goal with
         | |- context[@word.wrap _ ?word ?ok ?z] =>
           rewrite (@wrap_small _ word ok z) by lia
         | |- context[Z.of_nat (Z.to_nat ?z)] =>
           rewrite (Z2Nat.id z) by lia
         end;
  try lia.

Ltac word := solve [ word_cleanup ].

Theorem Z_u32 z :
  0 <= z < 2 ^ 32 ->
  uint.Z (W32 z) = z.
Proof.
  intros.
  unfold W32.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small; auto.
Qed.

Lemma u32_Z (x : u32) :
  W32 (uint.Z x) = x.
Proof.
  unfold W32. apply word.of_Z_unsigned.
Qed.

Theorem Z_u64 z :
  0 <= z < 2 ^ 64 ->
  uint.Z (W64 z) = z.
Proof.
  intros.
  unfold W64.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small; auto.
Qed.

Lemma u64_Z (x : u64) :
  W64 (uint.Z x) = x.
Proof.
  unfold W64. apply word.of_Z_unsigned.
Qed.

Lemma seq_U64_NoDup (m len : Z) :
  (0 ≤ m)%Z →
  (m+len < 2^64)%Z →
  NoDup (W64 <$> seqZ m len).
Proof.
  intros Hlb Hub. apply NoDup_fmap_2_strong; cycle 1.
  { apply NoDup_seqZ. }
  Set Printing Coercions. (* This is impossible to work on otherwise... *)
  clear- Hlb Hub. intros x y Hx%elem_of_seqZ Hy%elem_of_seqZ Heq.
  rewrite <-(Z_u64 x), <-(Z_u64 y).
  - by rewrite Heq.
  - word.
  - word.
Qed.

#[global]
Instance word_finite `(word: Interface.word width) {word_ok: word.ok word} : Finite word.
Proof.
  apply (enc_finite
    (λ w, uint.nat w)
    (λ n, word.of_Z (Z.of_nat n))
    (Z.to_nat (2^width))).
  - intros w. rewrite Z2Nat.id.
    + apply word.of_Z_unsigned.
    + apply word.unsigned_range.
  - intros w. apply Z2Nat.inj_lt.
    + apply word.unsigned_range.
    + apply Z.pow_nonneg. done.
    + apply word.unsigned_range.
  - intros n ?. rewrite word.unsigned_of_Z.
    rewrite wrap_small.
    + rewrite Nat2Z.id. done.
    + split.
      * apply Nat2Z.is_nonneg.
      * apply Nat2Z.inj_lt in H.
        rewrite Z2Nat.id in H; [done|].
        apply Z.pow_nonneg. done.
Qed.

Lemma word_wrap_bounds (width : Z) (word : Interface.word width) (word_ok : word.ok word) x :
  0 ≤ @word.wrap width word word_ok x < 2^width.
Proof.
  unfold word.wrap. split.
  - apply Z.mod_pos. apply Z.pow_pos_nonneg; [lia|].
    apply Z.lt_le_incl, word.width_pos.
  - apply Z_mod_lt. apply Z.lt_gt.
    apply Z.pow_pos_nonneg; [lia|].
    apply Z.lt_le_incl, word.width_pos.
Qed.

Definition u64_round_up (x div : u64) := let x' := word.add x div in word.mul (word.divu x' div) div.

Lemma u64_round_up_spec x div :
  uint.Z x + uint.Z div < 2^64 →
  uint.Z div > 0 →
  uint.Z (u64_round_up x div) `mod` (uint.Z div) = 0 ∧
  uint.Z x < uint.Z (u64_round_up x div) ∧
  uint.Z (u64_round_up x div) < 2^64.
Proof.
  intros. unfold u64_round_up.
  rewrite word.unsigned_mul, word.unsigned_divu. 2:word.
  rewrite word.unsigned_add.
  rewrite (wrap_small (_ + _)). 2:word.
  rewrite (wrap_small (_ `div` _)).
  2:{
    split.
    - apply Z_div_nonneg_nonneg; word.
    - assert (0 < word.unsigned div) as Hdiv by lia.
      pose proof (ZLib.Z.div_mul_undo_le (uint.Z x + uint.Z div) (uint.Z div) Hdiv) as Hdivle.
      lia. }
  rewrite wrap_small.
  2:{
    split.
    - apply Z.mul_nonneg_nonneg. 2:word. apply Z_div_nonneg_nonneg; word.
    - apply Z.lt_le_pred. etrans. 1: apply ZLib.Z.div_mul_undo_le. all: word. }
  split.
  { rewrite Z.mul_comm. apply ZLib.Z.Z_mod_mult'. }
  set (x' := uint.Z x).
  set (div' := uint.Z div).
  opose proof (Z.div_mod (x' + div') div' _) as Heq. 1:word.
  replace ((x' + div') `div` div' * div') with (x' + div' - (x' + div') `mod` div') by lia.
  assert ((x' + div') `mod` div' < div').
  { apply Z.mod_pos_bound. lia. }
  split.
  { apply Z.le_succ_l. lia. }
  assert (0 ≤ (x' + div') `mod` div'). 2:lia.
  apply Z_mod_nonneg_nonneg; word.
Qed.
