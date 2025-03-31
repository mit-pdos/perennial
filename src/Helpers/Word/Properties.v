From stdpp Require Import prelude.
From coqutil.Word Require Import Interface Properties.
From Perennial.Helpers.Word Require Import Integers Automation.

(* should maybe convert this into an explicit match on ints at some point *)
Definition u8_to_ascii (x:byte) : Ascii.ascii := Ascii.ascii_of_nat (uint.nat x).

(* conversion to string *)
Definition u8_to_string (x:byte) : String.string := String.String (u8_to_ascii x) String.EmptyString.

Definition u64_round_up (x div : u64) := let x' := word.add x div in word.mul (word.divu x' div) div.

Lemma seq_U64_NoDup (m len : Z) :
  0 ≤ m →
  m+len < 2^64 →
  NoDup (W64 <$> seqZ m len).
Proof.
  intros Hlb Hub. apply NoDup_fmap_2_strong.
  2:{ apply NoDup_seqZ. }
  setoid_rewrite elem_of_seqZ. intros; word.
Qed.

Lemma w64_to_nat_id x : W64 (Z.of_nat (uint.nat x)) = x.
Proof. word. Qed.

(* FIXME:(stdpp) These are missing from stdpp numbers.v *)
Global Instance Nat_ge_dec : RelDecision ge := ge_dec.
Global Instance Nat_gt_dec : RelDecision gt := gt_dec.
