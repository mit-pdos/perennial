From stdpp Require Import decidable countable finite.
From iris.proofmode Require Import proofmode.
From coqutil Require Import Datatypes.HList.
From coqutil.Z Require Import BitOps.
From coqutil.Word Require Naive.
From coqutil.Word Require Export Interface Properties.
From Perennial Require Import Helpers.LittleEndian.

Open Scope Z_scope.

(* TODO: separate some concerns in this file into three files:

- Create w64, w32, w8 types. These are constructed by using Naive.gen_word to
  create an instance of the word interface, then taking its carrier. (The actual
  carrier is a Z and a proof it's in-bounds.)
- word tactic and its helper lemmas.
- Little endian encoding and proofs. This can also have roundup I guess.

*)

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

#[global] Instance w64_word_instance : word 64 := (Naive.gen_word 64%Z shift_overflow_special_case_handlers).
#[global] Instance w64_word_instance_ok : word.ok w64_word_instance := Naive.gen_ok 64 _ eq_refl.
#[global] Instance w32_word_instance : word 32 := (Naive.gen_word 32%Z shift_overflow_special_case_handlers).
#[global] Instance w32_word_instance_ok : word.ok w32_word_instance := Naive.gen_ok 32 _ eq_refl.
#[global] Instance w8_word_instance : word 8 := (Naive.gen_word 8%Z shift_overflow_special_case_handlers).
#[global] Instance w8_word_instance_ok : word.ok w8_word_instance := Naive.gen_ok 8 _ eq_refl.

(* w64 needs to be a hard boundary (not a notation) to make coercions work. *)
Global SubClass w64 := @word.rep _ w64_word_instance.
Global SubClass w32 := @word.rep _ w32_word_instance.
Global SubClass w8 := @word.rep _ w8_word_instance.

Global Opaque w64_word_instance w32_word_instance w8_word_instance.

(* Ring does syntactic type matching (read: very simple matching) to see
if there's a matching ring structure.
As such, a "w64" looks different to it than a "word.rep _ w64_word_instance".
That's why we need two separate ring structures for each width.

This strategy will fail if we have an equality that mixes the two types.
E.g., "x = y.(z)", where "x : word.rep _ w64_word_instance" and "y" is an object
with field "hello : w64".
Syntactic type equality doesn't hold, and "unfold w64" doesn't work because
there isn't any w64 in sight. *)
Add Ring w64_rep_ring :
  (word.ring_theory (word := w64_word_instance))
  (preprocess [autorewrite with rew_word_morphism],
   morphism (word.ring_morph (word := w64_word_instance)),
   constants [Properties.word_cst]).

Add Ring w32_rep_ring :
  (word.ring_theory (word := w32_word_instance))
  (preprocess [autorewrite with rew_word_morphism],
   morphism (word.ring_morph (word := w32_word_instance)),
   constants [Properties.word_cst]).

Add Ring w8_rep_ring :
  (word.ring_theory (word := w8_word_instance))
  (preprocess [autorewrite with rew_word_morphism],
   morphism (word.ring_morph (word := w8_word_instance)),
   constants [Properties.word_cst]).

Add Ring w64_ring :
  (word.ring_theory (word := w64_word_instance) : (@ring_theory w64 _ _ _ _ _ _ (@eq w64)))
  (preprocess [autorewrite with rew_word_morphism],
   morphism (word.ring_morph (word := w64_word_instance)),
   constants [Properties.word_cst]).

Add Ring w32_ring :
  (word.ring_theory (word := w32_word_instance) : (@ring_theory w32 _ _ _ _ _ _ (@eq w32)))
  (preprocess [autorewrite with rew_word_morphism],
   morphism (word.ring_morph (word := w32_word_instance)),
   constants [Properties.word_cst]).

Add Ring w8_ring :
  (word.ring_theory (word := w8_word_instance) : (@ring_theory w8 _ _ _ _ _ _ (@eq w8)))
  (preprocess [autorewrite with rew_word_morphism],
   morphism (word.ring_morph (word := w8_word_instance)),
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

(* the u64_through* theorems are for backwards compatibility *)
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
  -(2^(width-1)) <= x < 2^(width-1) ->
  @word.swrap _ word x = x.
Proof.
  unfold word.swrap; intros.
  pose proof (ok.(word.width_pos)).
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
  rewrite swrap_small; auto.
  pose proof (word.signed_range x); lia.
Qed.

Theorem s32_to_s64_Z (x:w32) : sint.Z (W64 (sint.Z x)) = sint.Z x.
Proof.
  unfold W64.
  rewrite word.signed_of_Z.
  rewrite swrap_small; auto.
  pose proof (word.signed_range x); lia.
Qed.

Theorem s32_from_s64_Z (x: w64) : -2^(32-1) ≤ sint.Z x < 2^(32-1) ->
                                  sint.Z (W32 (sint.Z x)) = sint.Z x.
Proof.
  unfold W32; intros.
  rewrite word.signed_of_Z.
  rewrite swrap_small; auto.
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
  let t := split (byte:=w8_word_instance) w64_bytes n in
  tuple.to_list t.
Global Arguments u64_le : simpl never.

Definition le_to_u64 (l: list byte) : u64.
Proof.
  refine (word.of_Z _).
  set (t := tuple.of_list l).
  exact (combine (byte:=w8_word_instance) _ t).
Defined.

Lemma u64_le_0 : u64_le (W64 0) = replicate w64_bytes (W8 0).
Proof. reflexivity. Qed.

Theorem u64_le_length x : length (u64_le x) = w64_bytes.
Proof.
  reflexivity.
Qed.

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
  intros x; simpl.
  unfold le_to_u64, u64_le.
  rewrite -> tuple_of_to_list_u64.
  rewrite combine_split.
  change (Z.of_nat w64_bytes * 8) with 64.
  rewrite word.wrap_unsigned.
  rewrite word.of_Z_unsigned.
  done.
Qed.
(* end 64-bit code *)

(* this block is a copy-paste of the above with s/64/32/ *)
(** 32-bit encoding *)
Definition u32_le (x: u32) : list byte :=
  let n := word.unsigned x in
  let t := split (byte:=w8_word_instance) w32_bytes n in
  tuple.to_list t.
Global Arguments u32_le : simpl never.

Definition le_to_u32 (l: list byte) : u32.
Proof.
  refine (word.of_Z _).
  set (t := tuple.of_list l).
  exact (combine (byte:=w8_word_instance) _ t).
Defined.

Lemma u32_le_0 : u32_le (W32 0) = replicate w32_bytes (W8 0).
Proof. reflexivity. Qed.

Theorem u32_le_length x : length (u32_le x) = w32_bytes.
Proof.
  reflexivity.
Qed.

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
  intros x; simpl.
  unfold le_to_u32, u32_le.
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
  apply combine_bound.
Qed.

Lemma unsigned_U64 z : uint.Z (W64 z) = word.wrap (word:=w64_word_instance) z.
Proof.
  unfold W64; rewrite word.unsigned_of_Z; auto.
Qed.

Lemma unsigned_U32 z : uint.Z (W32 z) = word.wrap (word:=w32_word_instance) z.
Proof.
  unfold W32; rewrite word.unsigned_of_Z; auto.
Qed.

Lemma unsigned_U8 z : uint.Z (W8 z) = word.wrap (word:=w8_word_instance) z.
Proof.
  unfold W8; rewrite word.unsigned_of_Z; auto.
Qed.

Lemma signed_U64 z : sint.Z (W64 z) = word.swrap (word:=w64_word_instance) z.
Proof.
  unfold W64; rewrite word.signed_of_Z; auto.
Qed.

Lemma signed_U32 z : sint.Z (W32 z) = word.swrap (word:=w32_word_instance) z.
Proof.
  unfold W32; rewrite word.signed_of_Z; auto.
Qed.

Lemma w64_val_f_equal (x y: w64) :
  x = y →
  uint.Z x = uint.Z y ∧ sint.Z x = sint.Z y.
Proof. by intros ->. Qed.

Lemma w32_val_f_equal (x y: w32) :
  x = y →
  uint.Z x = uint.Z y ∧ sint.Z x = sint.Z y.
Proof. by intros ->. Qed.

Lemma w64_val_neq (x y: w64) :
  x ≠ y →
  uint.Z x ≠ uint.Z y ∧ sint.Z x ≠ sint.Z y.
Proof.
  intros Hne.
  split; intros Heq; contradiction Hne.
  - apply (inj uint.Z); auto.
  - apply (inj sint.Z); auto.
Qed.

Lemma f_not_equal {A B} (f: A → B) (x y: A) :
  f x ≠ f y →
  x ≠ y.
Proof. congruence. Qed.

Lemma word_unsigned_ltu {width: Z} (word: Interface.word width) {Hok: word.ok word} (x y: word) :
  word.ltu x y = bool_decide (uint.Z x < uint.Z y).
Proof.
  rewrite word.unsigned_ltu.
  destruct (Z.ltb_spec0 (uint.Z x) (uint.Z y)).
  - rewrite bool_decide_eq_true_2; auto.
  - rewrite bool_decide_eq_false_2; auto.
Qed.

Definition w64_unsigned_ltu : ∀ (x y: w64), _ := word_unsigned_ltu w64_word_instance.

Lemma w32_val_neq (x y: w32) :
  x ≠ y →
  uint.Z x ≠ uint.Z y ∧ sint.Z x ≠ sint.Z y.
Proof.
  intros Hne.
  split; intros Heq; contradiction Hne.
  - apply (inj uint.Z); auto.
  - apply (inj sint.Z); auto.
Qed.

Create HintDb word.

Hint Rewrite unsigned_U64 unsigned_U32 unsigned_U8 : word.

Ltac simpl_word_constants :=
  repeat match goal with
         | [ H: context[word.unsigned (W64 ?x)] |- _ ] => change (uint.Z x) with x in H
         | [ |- context[word.unsigned (W64 ?x)] ] => change (uint.Z x) with x
         | [ H: context[word.unsigned (W32 ?x)] |- _ ] => change (uint.Z (W32 x)) with x in H
         | [ |- context[word.unsigned (W32 ?x)] ] => change (uint.Z (W32 x)) with x
         | [ H: context[word.unsigned (W8 ?x)] |- _ ] => change (uint.Z (W32 8)) with x in H
         | [ |- context[word.unsigned (W8 ?x)] ] => change (uint.Z (W8 x)) with x
        (* TODO: add sint versions *)
    end.

Ltac word_cleanup_core :=
  (* this is so that the following pattern succeeds when (for some reason)
  instead of w64 we have its unfolding *)
  fold w64 w32 w8 in *;
  repeat autounfold with word in *;
  try lazymatch goal with
      (* TODO: this isn't the right strategy if the numbers in the goal are used
      signed. [word] can try both via backtracking, but this can't be part of
      "cleanup".  *)
      | |- @eq u64 _ _ => apply word.unsigned_inj
      | |- @eq u32 _ _ => apply word.unsigned_inj
      | |- @eq u8 _ _ => apply word.unsigned_inj
      | |- not (@eq u64 _ _) => apply (f_not_equal uint.Z)
      | |- not (@eq u32 _ _) => apply (f_not_equal uint.Z)
      | |- not (@eq u8 _ _) => apply (f_not_equal uint.Z)
      end;
  simpl_word_constants;
  (* can't replace some of these with [autorewrite], probably because typeclass inference
  isn't the same *)
  repeat (
      rewrite -> ?word.unsigned_add, ?word.unsigned_sub,
        ?word.unsigned_divu_nowrap, ?word.unsigned_modu_nowrap,
        ?word.unsigned_mul,
        ?w64_unsigned_ltu
      || rewrite -> ?word.unsigned_of_Z, ?word.of_Z_unsigned in *
      || autorewrite with word in *
    );
  repeat match goal with
         | _ => progress simpl_word_constants
         | [ H: @eq w64 _ _ |- _ ] => let H' := fresh H "_signed" in
                                      apply w64_val_f_equal in H as [H H']
         | [ H: @eq w32 _ _ |- _ ] => let H' := fresh H "_signed" in
                                      apply w32_val_f_equal in H as [H H']
         | [ H: not (@eq w64 _ _) |- _ ] => let H' := fresh H "_signed" in
                                      apply w64_val_neq in H as [H H']
         | [ H: @eq w32 _ _ |- _ ] => let H' := fresh H "_signed" in
                                      apply w32_val_neq in H as [H H']
         end;
  repeat match goal with
         | [ |- context[uint.Z ?x] ] =>
           lazymatch goal with
           | [ H': 0 <= uint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.unsigned_range x)
           end
         | [ H: context[uint.Z ?x] |- _ ] =>
           lazymatch goal with
           | [ H': 0 <= uint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.unsigned_range x)
           end
         | [ |- context[sint.Z ?x] ] =>
           lazymatch goal with
           | [ H': - (2^ _) ≤ sint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.signed_range x)
           end
         | [ H: context[sint.Z ?x] |- _ ] =>
           lazymatch goal with
           | [ H': - (2^ _) ≤ sint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.signed_range x)
           end
         end;
  repeat match goal with
         | |- context[@word.wrap _ ?word ?ok ?z] =>
           rewrite -> (@wrap_small _ word ok z) by lia
         | |- context[@word.swrap _ ?word ?ok ?z] =>
           rewrite -> (@swrap_small _ word ok z) by lia
         | |- context[Z.of_nat (Z.to_nat ?z)] =>
           rewrite -> (Z2Nat.id z) by lia
         end.

(* TODO: only for backwards compatibility.

[word_cleanup] should be be replaced with a new tactic
that does a subset of safe and useful rewrites *)
Ltac word_cleanup := word_cleanup_core; try lia.

Ltac word := first [
                 solve [
                     try iPureIntro;
                     word_cleanup_core;
                     unfold word.wrap in *;
                     (* NOTE: some inefficiency here because [lia] will do [zify]
                 again, but we can't rebind the zify hooks in Ltac *)
                     zify; Z.div_mod_to_equations; lia
                   ]
               | fail 1 "word could not solve goal"
               ].

Theorem Z_u32 z :
  0 <= z < 2 ^ 32 ->
  uint.Z (W32 z) = z.
Proof. word. Qed.

Lemma u32_Z (x : u32) :
  W32 (uint.Z x) = x.
Proof. word. Qed.

Theorem Z_u64 z :
  0 <= z < 2 ^ 64 ->
  uint.Z (W64 z) = z.
Proof. word. Qed.

Lemma u64_Z (x : u64) :
  W64 (uint.Z x) = x.
Proof. word. Qed.

Lemma w64_to_nat_id (x : w64) :
  W64 (Z.of_nat (uint.nat x)) = x.
Proof. word. Qed.

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
  rewrite -> word.unsigned_mul_nowrap, word.unsigned_divu_nowrap by word.
  rewrite -> word.unsigned_add_nowrap by word.
  split.
  { rewrite Z.mul_comm. apply ZLib.Z.Z_mod_mult'. }
  word.
Qed.

Lemma nat_thru_w64_id (x : nat) :
  Z.of_nat x < 2^64 ->
  uint.nat (W64 (Z.of_nat x)) = x.
Proof. word. Qed.
