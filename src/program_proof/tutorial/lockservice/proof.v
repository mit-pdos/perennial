From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.tutorial Require Import lockservice.

(* This is boilerplate. *)

Section marshal_proof.
Context `{!heapGS Σ}.

(* TODO: copied this naming convention from "u64_le". What does le actually
   mean? *)
Definition bool_le (b:bool) : list u8 := if b then [U8 1] else [U8 0].

Lemma wp_EncodeBool (b:bool) :
  {{{ True }}}
    EncodeBool #b
  {{{ sl, RET (slice_val sl); is_slice sl byteT 1 (bool_le b) }}}
.
Proof.
Admitted.

Lemma wp_DecodeBool sl b q :
  {{{ is_slice sl byteT q (bool_le b) }}}
    DecodeBool (slice_val sl)
  {{{ RET #b; True }}}
.
Proof.
Admitted.

Lemma wp_EncodeUint64 x:
  {{{ True }}}
    EncodeUint64 #x
  {{{ sl, RET (slice_val sl); is_slice sl byteT 1 (u64_le x) }}}
.
Proof.
Admitted.

Lemma wp_DecodeUint64 sl x q :
  {{{ is_slice sl byteT q (u64_le x) }}}
    DecodeBool (slice_val sl)
  {{{ RET #x; is_slice sl byteT q (u64_le x) }}}
.
Proof.
Admitted.

End marshal_proof.
