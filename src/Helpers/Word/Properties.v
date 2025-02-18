From stdpp Require Import prelude.
From coqutil.Word Require Import Interface Properties.
From Perennial.Helpers.Word Require Import Integers.

(* should maybe convert this into an explicit match on ints at some point *)
Definition u8_to_ascii (x:byte) : Ascii.ascii := Ascii.ascii_of_nat (uint.nat x).

(* conversion to string *)
Definition u8_to_string (x:byte) : String.string := String.String (u8_to_ascii x) String.EmptyString.

Definition u64_round_up (x div : u64) := let x' := word.add x div in word.mul (word.divu x' div) div.

Theorem u64_Z_through_nat (x:w64) : Z.of_nat (uint.nat x) = uint.Z x.
Proof.
  pose proof (word.unsigned_range x); lia.
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
