From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export config.
From Perennial.program_proof Require Import marshal_stateless_proof.

Module Config.
Section Config.

Definition C := list u64.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded u64_le (length args) ++ concat (u64_le <$> args).

Context `{!heapGS Σ}.

Definition own conf_sl (conf:list u64) : iProp Σ :=
  "Hargs_state_sl" ∷ is_slice_small conf_sl uint64T 1 conf.

Lemma wp_Encode conf_sl (conf:C) :
  {{{
        own conf_sl conf
  }}}
    config.EncodeConfig (slice_val conf_sl)
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc conf⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}.
Proof.
  iIntros (Φ) "Hconf HΦ".
  wp_call.
  iDestruct (is_slice_small_sz with "Hconf") as %Hsz.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (enc_ptr) "Henc_sl".
  simpl.
  replace (int.nat 0) with (0%nat) by word.
  simpl.

  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc) "Henc".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_load.
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (enc_sl) "Henc_sl".
  wp_store.
  simpl.

  replace (conf_sl.(Slice.sz)) with (U64 (length conf)) by word.
  set (P:=(λ (i:u64),
      "Henc" ∷ is_slice enc_sl byteT 1 ((u64_le (length conf)) ++ concat (u64_le <$> (take (int.nat i) conf))) ∗
      "Henc" ∷ True
    )%I)
  .
  wp_apply (wp_forSlice P with "[] [$Hconf]").
  {
    iIntros (i srv).
    clear Φ.
    iIntros (Φ) "!# (HP & %Hi & %Hlookup) HΦ".
Admitted.

Lemma wp_Decode enc enc_sl (conf:C) :
  {{{
        ⌜has_encoding enc conf⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}
    config.DecodeConfig (slice_val enc_sl)
  {{{
        conf_sl, RET (slice_val conf_sl); own conf_sl conf
  }}}.
Admitted.

End Config.
End Config.
