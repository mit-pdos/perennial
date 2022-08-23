From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export config.
From Perennial.program_proof Require Import marshal_stateless_proof.

Module Config.
Section Config.

Definition C := list u64.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = u64_le (length args) ++ concat (u64_le <$> args).

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
      ∃ enc_sl,
      "Henc_sl" ∷ is_slice enc_sl byteT 1 ((u64_le (length conf)) ++ concat (u64_le <$> (take (int.nat i) conf))) ∗
      "Henc" ∷ enc ↦[slice.T byteT] (slice_val enc_sl)
    )%I)
  .
  wp_apply (wp_forSlice P with "[] [$Hconf Henc Henc_sl]").
  {
    iIntros (i srv).
    clear Φ.
    iIntros (Φ) "!# (HP & %Hi_bound & %Hlookup) HΦ".
    iNamed "HP".

    wp_pures.
    wp_load.
    wp_apply (wp_WriteInt with "Henc_sl").
    iIntros (enc_sl') "Henc_sl".
    wp_store.
    iModIntro.
    iApply "HΦ".
    unfold P.
    iExists _; iFrame "Henc".
    iApply to_named.
    iExactEq "Henc_sl".
    f_equal.

    (* Start pure proof *)
    (* prove that appending the encoded next entry results in a concatenation of
       the first (i+1) entries *)
    rewrite -app_assoc.
    f_equal.
    replace (u64_le srv) with (concat (u64_le <$> [srv])) by done.
    rewrite -concat_app.
    rewrite -fmap_app.
    replace (int.nat (word.add i 1)) with (int.nat i + 1)%nat by word.
    f_equal.
    f_equal.
    (* TODO: list_solver *)
    rewrite take_more; last word.
    f_equal.
    apply list_eq.
    intros.
    destruct i0.
    {
      simpl.
      rewrite lookup_take; last lia.
      rewrite lookup_drop.
      rewrite -Hlookup.
      f_equal.
      word.
    }
    {
      simpl.
      rewrite lookup_nil.
      rewrite lookup_take_ge; last word.
      done.
    }
    (* End pure proof *)
  }
  {
    unfold P.
    iExists _; iFrame.
  }
  iIntros "[HP Hconf_sl]".
  iNamed "HP".
  wp_pures.
  wp_load.
  iApply "HΦ".
  iModIntro.
  iFrame.
  rewrite -Hsz.
  iPureIntro.
  unfold has_encoding.
  rewrite firstn_all.
  done.
Qed.

Lemma wp_Decode enc enc_sl (conf:C) :
  {{{
        ⌜has_encoding enc conf⌝ ∗
        is_slice_small enc_sl byteT 1 enc
  }}}
    config.DecodeConfig (slice_val enc_sl)
  {{{
        conf_sl, RET (slice_val conf_sl); own conf_sl conf
  }}}.
Proof.
  iIntros (Φ) "[%Henc Henc_sl] HΦ".
  wp_call.
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (configLen_ptr) "HconfigLen".
  wp_pures.
  wp_load.
  rewrite Henc.
  wp_apply (wp_ReadInt with "[$Henc_sl]").
  iIntros (enc_sl') "Henc_sl".
  wp_store.
  wp_store.

  wp_load.
  wp_apply (wp_NewSlice).
  iIntros (conf_sl) "Hconf_sl".
  wp_pures.

  set (P:=(λ (i:u64),
      ∃ enc_sl,
      "Henc_sl" ∷ is_slice enc_sl byteT 1 (concat (u64_le <$> (drop (int.nat i) conf))) ∗
      "Henc" ∷ enc_ptr ↦[slice.T byteT] (slice_val enc_sl)
    )%I)
  .
Admitted.

End Config.
End Config.
