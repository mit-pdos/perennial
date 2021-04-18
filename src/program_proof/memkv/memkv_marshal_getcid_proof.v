From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Export common_proof.


Section memkv_marshal_getcid_proof.

Context `{!heapG Σ, rpcG Σ GetReplyC}.

Definition has_encoding_CID (data:list u8) (cid:u64) : Prop.
Admitted.

Lemma wp_encodeCID cid :
  {{{
       True
  }}}
    encodeCID #cid
  {{{
       sl data, RET (slice_val sl); typed_slice.is_slice sl byteT 1%Qp data ∗
                                                         ⌜has_encoding_CID data cid⌝
  }}}
.
Proof.
Admitted.

Lemma wp_decodeCID sl data cid :
  {{{
       typed_slice.is_slice sl byteT 1%Qp data ∗ ⌜has_encoding_CID data cid⌝
  }}}
    decodeCID (slice_val sl)
  {{{
       RET #(cid); True
  }}}
.
Proof.
Admitted.

End memkv_marshal_getcid_proof.
