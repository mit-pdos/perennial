From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import cryptoutil.

From Perennial.program_proof.pav Require Import cryptoffi.

Section proof.
Context `{!heapGS Σ}.

Lemma wp_Hash sl_b b d0 :
  {{{
    "Hsl_b" ∷ own_slice_small sl_b byteT d0 b
  }}}
  Hash (slice_val sl_b)
  {{{
    sl_hash hash, RET (slice_val sl_hash);
    "Hsl_b" ∷ own_slice_small sl_b byteT d0 b ∗
    "Hhash" ∷ own_slice_small sl_hash byteT (DfracOwn 1) hash ∗
    "#His_hash" ∷ is_hash b hash
  }}}.
Proof.
  iIntros (Φ) "H HΦ". wp_rec. iNamed "H".
  wp_apply wp_NewHasher. iIntros (?). iNamed 1.
  wp_apply (wp_Hasher__Write with "[$]"). iNamed 1.
  wp_apply (wp_Hasher__Sum Slice.nil with "[$Hown_hr]").
  { iApply own_slice_zero. }
  iIntros (??). iNamed 1.
  iDestruct (own_slice_to_small with "Hsl_b_out") as "Hsl_b_out".
  iApply "HΦ". iFrame "∗#".
Qed.

End proof.
