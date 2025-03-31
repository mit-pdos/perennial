From Coq Require Import ZArith.
From stdpp Require Import decidable countable finite.
From coqutil.Z Require Import BitOps.
From coqutil.Word Require Naive.
From coqutil.Word Require Import Interface Properties.

Open Scope Z_scope.
Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

(*
Define the w64, w32, w8 types. These are constructed by using Naive.gen_word to
  create an instance of the word interface, then taking its carrier. (The actual
  carrier is a Z and a proof it's in-bounds.)

This file also defines ring structures over each of these types.
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

#[global] Opaque w64_word_instance w32_word_instance w8_word_instance.

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

#[global] Instance w64_eq_dec : EqDecision w64 := _.
#[global] Instance w32_eq_dec : EqDecision w32 := _.
#[global] Instance w8_eq_dec : EqDecision w8 := _.

#[global]
Instance word_countable `(word: Interface.word width) {word_ok: word.ok word} : Countable word.
Proof.
  apply (inj_countable'
           word.unsigned
           (fun z => word.of_Z z)); intros.
  by rewrite word.of_Z_unsigned.
Qed.

#[global] Instance w64_countable : Countable w64.
Proof. apply _. Qed.
#[global] Instance w32_countable : Countable w32.
Proof. apply _. Qed.
#[global] Instance w8_countable : Countable byte.
Proof. apply _. Qed.

Module uint.
  Notation Z := word.unsigned.
  Notation nat x := (Z.to_nat (Z x)).
End uint.

Module sint.
  Notation Z := word.signed.
End sint.

#[global] Instance int_Z_inj `(word: Interface.word width) {word_ok: word.ok word} :
  Inj eq eq (@word.unsigned width _).
Proof.
  intros x1 x2.
  intros.
  apply word.unsigned_inj in H; auto.
Qed.

#[global] Instance sint_Z_inj `(word: Interface.word width) {word_ok: word.ok word} :
  Inj eq eq (@word.signed width _).
Proof.
  intros x1 x2.
  intros.
  apply word.signed_inj in H; auto.
Qed.

Lemma word_wrap_bounds (width : Z) (word : Interface.word width) (word_ok : word.ok word) x :
  0 ≤ @word.wrap width word word_ok x < 2^width.
Proof.
  pose proof word.width_pos.
  unfold word.wrap. lia.
Qed.

Lemma wrap_small `{word: Interface.word width} {ok: word.ok word} (x:Z) :
  0 <= x < 2^width ->
  word.wrap x = x.
Proof.
  unfold word.wrap; intros.
  rewrite Zmod_small; auto.
Qed.

Lemma swrap_small `{word: Interface.word width} {ok: word.ok word} (x:Z) :
  -(2^(width-1)) <= x < 2^(width-1) ->
  @word.swrap _ word x = x.
Proof.
  pose proof word.width_pos.
  unfold word.swrap; intros.
  unshelve epose proof ZLib.Z.pow2_times2 width _; first by lia.
  rewrite Zmod_small; lia.
Qed.

#[global]
Instance word_finite `(word: Interface.word width) {word_ok: word.ok word} :
  Finite word.
Proof.
  apply (enc_finite
    (λ w, Z.to_nat $ uint.Z w)
    (λ n, word.of_Z (Z.of_nat n))
    (Z.to_nat (2^width))).
  - intros w. pose proof (word.unsigned_range w).
    rewrite Z2Nat.id.
    + rewrite word.of_Z_unsigned; auto.
    + lia.
  - intros w. pose proof (word.unsigned_range w).
    lia.
  - intros n ?. rewrite word.unsigned_of_Z.
    rewrite wrap_small; lia.
Qed.
