From Perennial.Helpers Require Import List.

From Goose.github_com.tchajed Require Import marshal.
From Perennial.goose_lang.lib Require Import encoding.

From Perennial.program_proof Require Import proof_prelude std_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section goose_lang.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}.

Implicit Types (v:val).

Theorem wp_ReadInt s q x tail :
  {{{ is_slice_small s byteT q (u64_le x ++ tail) }}}
    ReadInt (slice_val s)
  {{{ s', RET (#x, slice_val s'); is_slice_small s' byteT q tail }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_lam.
  wp_apply (wp_UInt64Get_unchanged with "Hs").
  { rewrite /list.untype fmap_app take_app_alt //. }
  iIntros "Hs".
  wp_apply (wp_SliceSkip_small with "Hs").
  { rewrite /list.untype fmap_length app_length /=. word. }
  iIntros (s') "Hs'". wp_pures. iApply "HΦ". done.
Qed.

Local Theorem wp_compute_new_cap (old_cap min_cap : u64) :
  {{{ True }}}
    compute_new_cap #old_cap #min_cap
  {{{ (new_cap : u64), RET #new_cap; ⌜int.Z min_cap ≤ int.Z new_cap⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_call.
  wp_apply wp_ref_to. { val_ty. }
  iIntros (l) "Hl". wp_pures.
  wp_load.
  wp_if_destruct.
  - wp_store. wp_load. iApply "HΦ". iPureIntro. done.
  - wp_load. iApply "HΦ". iPureIntro. word.
Qed.

Local Theorem wp_reserve s (extra : u64) (vs : list u8) :
  {{{ is_slice s byteT 1 vs }}}
    reserve (slice_val s) #extra
  {{{ s', RET slice_val s'; ⌜int.Z extra ≤ Slice.extra s'⌝ ∗ is_slice s' byteT 1 vs }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_lam.
  iDestruct (is_slice_wf with "Hs") as %Hwf.
  iDestruct (is_slice_sz with "Hs") as %Hsz.
  wp_apply wp_slice_len.
  wp_apply wp_SumAssumeNoOverflow. iIntros (Hsum).
  wp_pures. wp_apply wp_slice_cap.
  wp_if_destruct.
  - (* we have to grow. *)
    wp_apply wp_slice_cap.
    wp_apply wp_compute_new_cap.
    iIntros (new_cap Hcap).
    wp_apply wp_slice_len.
    wp_apply wp_new_slice_cap; first done.
    { word. }
    iIntros (ptr) "Hnew". wp_pures.
    iDestruct (slice.is_slice_to_small with "Hs") as "Hs".
    iDestruct (slice.is_slice_small_acc with "Hnew") as "[Hnew Hcl]".
    wp_apply (wp_SliceCopy_full with "[Hnew Hs]").
    { iFrame. iPureIntro. rewrite list_untype_length Hsz replicate_length //. }
    iIntros "[_ Hnew]". iDestruct ("Hcl" with "Hnew") as "Hnew".
    wp_pures. iApply "HΦ". iModIntro. iFrame. iPureIntro. simpl. word.
  - (* already big enough *)
    iApply "HΦ". iFrame. iPureIntro. word.
Qed.

Theorem wp_WriteInt s x (vs : list u8) :
  {{{ is_slice s byteT 1 vs }}}
    WriteInt (slice_val s) #x
  {{{ s', RET slice_val s'; is_slice s' byteT 1 (vs ++ u64_le x) }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_lam. wp_pures.
  wp_apply (wp_reserve with "Hs"). clear s. iIntros (s) "[% Hs]". wp_pures.
  iDestruct (is_slice_wf with "Hs") as %Hwf.
  iDestruct (is_slice_sz with "Hs") as %Hsz.
  wp_apply wp_slice_len. wp_pures.
  wp_apply (wp_SliceTake_full_cap with "Hs").
  { word. }
  iIntros (ex) "[%Hex Hsl]".
  set (s' := slice_take _ _).
  wp_apply wp_SliceSkip.
  { rewrite /slice_take /=. word. }
  iDestruct (slice.is_slice_split_acc s.(Slice.sz) with "Hsl") as "[Hsl Hclose]".
  { len. }
  wp_apply (wp_UInt64Put with "Hsl").
  { len. rewrite Hex. word. }
  iIntros "Hsl". iDestruct ("Hclose" with "Hsl") as "Hsl".
  wp_pures. iApply "HΦ". iModIntro.
  rewrite /is_slice. iExactEq "Hsl". repeat f_equal.
  rewrite /list.untype fmap_app. f_equal.
  { rewrite take_app_alt //. len. }
  rewrite drop_ge //. len. rewrite Hex. word.
Qed.

Theorem wp_WriteBytes s (vs : list u8) data_sl q (data : list u8) :
  {{{ is_slice s byteT 1 vs ∗ is_slice_small data_sl byteT q data }}}
    WriteBytes (slice_val s) (slice_val data_sl)
  {{{ s', RET slice_val s';
    is_slice s' byteT 1 (vs ++ data) ∗
    is_slice_small data_sl byteT q data
  }}}.
Proof.
  iIntros (Φ) "[Hs Hdata] HΦ". wp_lam. wp_pures.
  wp_apply wp_slice_len.
  wp_apply (wp_reserve with "Hs"). clear s. iIntros (s) "[% Hs]". wp_pures.
  iDestruct (is_slice_wf with "Hs") as %Hwf.
  iDestruct (is_slice_sz with "Hs") as %Hsz.
  iDestruct (is_slice_small_sz with "Hdata") as %Hdatasz.
  wp_apply wp_slice_len. wp_pures.
  wp_apply wp_slice_len.
  wp_apply (wp_SliceTake_full_cap with "Hs").
  { word. }
  iIntros (ex) "[%Hex Hsl]".
  set (s' := slice_take _ _).
  wp_apply wp_SliceSkip.
  { rewrite /slice_take /=. word. }
  iDestruct (slice.is_slice_split_acc s.(Slice.sz) with "Hsl") as "[Hsl Hclose]".
  { len. }
  wp_apply (wp_SliceCopy_full with "[$Hdata $Hsl]").
  { iPureIntro. len. rewrite Hdatasz Hex. word. }
  iIntros "[Hdata Hsl]". iDestruct ("Hclose" with "Hsl") as "Hsl".
  wp_pures. iApply "HΦ". iFrame "Hdata". iModIntro.
  rewrite /is_slice. iExactEq "Hsl". repeat f_equal.
  rewrite /list.untype fmap_app. f_equal.
  rewrite take_app_alt //. len.
Qed.

End goose_lang.
