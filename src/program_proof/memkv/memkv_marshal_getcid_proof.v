From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.program_proof.memkv Require Export common_proof.

Section memkv_marshal_getcid_proof.

Definition has_encoding_Uint64 (data:list u8) (cid:u64) : Prop :=
  has_encoding data [ EncUInt64 cid ].

Context `{!heapGS Σ}.

Lemma wp_EncodeUint64 cid :
  {{{
       True
  }}}
    EncodeUint64 #cid
  {{{
       sl data, RET (slice_val sl); typed_slice.own_slice sl byteT (DfracOwn 1) data ∗
                                                         ⌜has_encoding_Uint64 data cid⌝
  }}}
.
Proof.
  iIntros (Φ) "Hrep HΦ".

  wp_lam.
  wp_pures.
  iNamed "Hrep".

  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.

  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.

  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (rep_sl repData).
  iIntros "(%Henc & %Hlen & Hrep_sl)".
  iApply "HΦ".
  iFrame.
  iPureIntro.
  rewrite /has_encoding_Uint64.
  done.
Qed.


Lemma wp_DecodeUint64' sl data cid q :
  {{{
       typed_slice.own_slice_small sl byteT q data ∗ ⌜has_encoding_Uint64 data cid⌝
  }}}
    DecodeUint64 (slice_val sl)
  {{{
       RET #(cid); True
  }}}
.
Proof.
  iIntros (Φ) "[Hsl %Henc] HΦ".
  wp_lam.
  wp_pures.

  wp_apply (wp_new_dec with "[$Hsl]").
  { done. }
  iIntros (?) "Hdec".
  wp_pures.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".

  iApply "HΦ".
  by iFrame.
Qed.

Lemma wp_DecodeUint64 sl data cid q :
  {{{
       typed_slice.own_slice sl byteT q data ∗ ⌜has_encoding_Uint64 data cid⌝
  }}}
    DecodeUint64 (slice_val sl)
  {{{
       RET #(cid); True
  }}}
.
Proof.
  iIntros (Φ) "[Hsl %Henc] HΦ".
  iDestruct (typed_slice.own_slice_small_acc with "Hsl") as "[Hsl _]".
  wp_apply (wp_DecodeUint64' with "[$Hsl //]").
  by iApply "HΦ".
Qed.

End memkv_marshal_getcid_proof.
