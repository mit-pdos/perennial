From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.memkv Require Export common_proof.

Section memkv_marshal_getcid_proof.

Definition has_encoding_Uint64 (data:list u8) (cid:u64) : Prop.
Admitted.

Context `{!heapG Σ}.

Lemma wp_encodeUint64 cid :
  {{{
       True
  }}}
    encodeUint64 #cid
  {{{
       sl data, RET (slice_val sl); typed_slice.is_slice sl byteT 1%Qp data ∗
                                                         ⌜has_encoding_Uint64 data cid⌝
  }}}
.
Proof.
Admitted.

Lemma wp_decodeUint64 sl data cid :
  {{{
       typed_slice.is_slice sl byteT 1%Qp data ∗ ⌜has_encoding_Uint64 data cid⌝
  }}}
    decodeUint64 (slice_val sl)
  {{{
       RET #(cid); True
  }}}
.
Proof.
Admitted.

End memkv_marshal_getcid_proof.
