From stdpp Require Import prelude.
From iris.proofmode Require Import proofmode.
From coqutil.Word Require Import Interface Properties.
From Perennial.Helpers.Word Require Import Integers Properties.

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

Lemma test_nat_thru_w64_id (x : nat) :
  Z.of_nat x < 2^64 ->
  uint.nat (W64 (Z.of_nat x)) = x.
Proof. word. Qed.

(* TODO: these lemmas aren't really part of the automation, but are proven using
[word]. They should go somewhere else. *)

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
