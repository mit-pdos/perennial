From Perennial.Helpers Require Import List.

From Goose.github_com.tchajed Require Import marshal.
From Perennial.goose_lang.lib Require Import encoding.

From Perennial.program_proof Require Import proof_prelude std_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section goose_lang.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}.

Implicit Types (v:val).

Theorem wp_ReadInt s q x tail :
  {{{ own_slice_small s byteT q (u64_le x ++ tail) }}}
    ReadInt (slice_val s)
  {{{ s', RET (#x, slice_val s'); own_slice_small s' byteT q tail }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_lam.
  wp_apply (wp_UInt64Get_unchanged with "Hs").
  { rewrite /list.untype fmap_app take_app_length' //. }
  iIntros "Hs".
  wp_apply (wp_SliceSkip_small with "Hs").
  { rewrite /list.untype fmap_length app_length /=. word. }
  iIntros (s') "Hs'". wp_pures. iApply "HΦ". done.
Qed.

Theorem wp_ReadBytes s q (len: u64) (head tail : list u8) :
  length head = uint.nat len →
  {{{ own_slice_small s byteT q (head ++ tail) }}}
    ReadBytes (slice_val s) #len
  {{{ b s' q', RET (slice_val b, slice_val s'); own_slice_small b byteT q' head ∗ own_slice_small s' byteT q' tail }}}.
Proof.
  iIntros (Hlen Φ) "Hs HΦ".
  iMod (own_slice_small_persist with "Hs") as "#Hs".
  wp_call.
  wp_apply (wp_SliceTake_small with "Hs").
  { rewrite /list.untype fmap_app app_length !fmap_length. word. }
  iIntros "Hs1".
  wp_apply (wp_SliceSkip_small with "Hs").
  { rewrite /list.untype fmap_length app_length /=. word. }
  iIntros (s') "Hs2". wp_pures. iApply "HΦ".
  { rewrite /list.untype -fmap_take -fmap_drop.
    rewrite take_app_length' // drop_app_length' //. iFrame. done. }
Qed.

Theorem wp_ReadBytesCopy s q (len: u64) (head tail : list u8) :
  length head = uint.nat len →
  {{{ own_slice_small s byteT q (head ++ tail) }}}
    ReadBytesCopy (slice_val s) #len
  {{{ b s', RET (slice_val b, slice_val s'); own_slice b byteT (DfracOwn 1) head ∗ own_slice_small s' byteT q tail }}}.
Proof.
  iIntros (Hlen Φ) "Hs HΦ". wp_call.
  wp_apply wp_NewSlice. iIntros (b) "Hb".
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  iDestruct (own_slice_small_wf with "Hs") as %Hwf.
  rewrite app_length in Hsz.
  wp_apply wp_SliceTake.
  { word. }
  iDestruct (slice_small_split _ len with "Hs") as "[Hs Hsclose]".
  { rewrite app_length. word. }
  iDestruct (own_slice_small_acc with "Hb") as "[Hb Hbclose]".
  wp_apply (wp_SliceCopy_full with "[$Hs $Hb]").
  { iPureIntro. rewrite !list_untype_length replicate_length take_length app_length. word. }
  iIntros "[Hs Hb]".
  iDestruct (own_slice_combine with "Hs Hsclose") as "Hs".
  { word. }
  rewrite take_drop.
  wp_apply (wp_SliceSkip_small with "Hs").
  { rewrite list_untype_length app_length. word. }
  iIntros (s') "Hs'".
  wp_pures. iApply "HΦ". iModIntro. iSplitR "Hs'".
  - iApply "Hbclose". rewrite take_app_length' //.
  - rewrite /list.untype -fmap_drop drop_app_length' //.
Qed.

Theorem wp_ReadBool s q (bit: u8) (tail: list u8) :
  {{{ own_slice_small s byteT q (bit :: tail) }}}
    ReadBool (slice_val s)
  {{{ (b: bool) s', RET (#b, slice_val s');
      ⌜b = bool_decide (uint.Z bit ≠ 0)⌝ ∗
      own_slice_small s' byteT q tail }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_call.
  wp_apply (wp_SliceGet with "[$Hs]"); [ auto | ].
  iIntros "Hs".
  wp_pures.
  (* TODO: this wp seems to come from untyped library *)
  wp_apply (wp_SliceSkip_small with "Hs").
  { rewrite list_untype_length /=. word. }
  iIntros (s') "Hs".
  wp_pures. iModIntro.
  iApply "HΦ".
  iSplit.
  { iPureIntro. rewrite -bool_decide_not !bool_decide_decide.
    assert (#bit ≠ #(U8 0) ↔ uint.Z bit ≠ 0).
    { apply not_iff_compat.
      split.
    - inversion 1; subst; auto.
    - intros H.
      do 2 f_equal.
      apply (inj uint.Z). (* don't know how I even figured this out *)
      change (uint.Z (U8 0)) with 0%Z; assumption.
    }
    destruct (decide _), (decide _); auto; tauto.
  }
  iApply "Hs".
Qed.

Local Theorem wp_compute_new_cap (old_cap min_cap : u64) :
  {{{ True }}}
    compute_new_cap #old_cap #min_cap
  {{{ (new_cap : u64), RET #new_cap; ⌜uint.Z min_cap ≤ uint.Z new_cap⌝ }}}.
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
  {{{ own_slice s byteT (DfracOwn 1) vs }}}
    reserve (slice_val s) #extra
  {{{ s', RET slice_val s'; ⌜uint.Z extra ≤ Slice.extra s'⌝ ∗ own_slice s' byteT (DfracOwn 1) vs }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_lam.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  iDestruct (own_slice_sz with "Hs") as %Hsz.
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
    iDestruct (slice.own_slice_to_small with "Hs") as "Hs".
    iDestruct (slice.own_slice_small_acc with "Hnew") as "[Hnew Hcl]".
    wp_apply (wp_SliceCopy_full with "[Hnew Hs]").
    { iFrame. iPureIntro. rewrite list_untype_length Hsz replicate_length //. }
    iIntros "[_ Hnew]". iDestruct ("Hcl" with "Hnew") as "Hnew".
    wp_pures. iApply "HΦ". iModIntro. iFrame. iPureIntro. simpl. word.
  - (* already big enough *)
    iApply "HΦ". iFrame. iPureIntro. word.
Qed.

Theorem wp_WriteInt s x (vs : list u8) :
  {{{ own_slice s byteT (DfracOwn 1) vs }}}
    WriteInt (slice_val s) #x
  {{{ s', RET slice_val s'; own_slice s' byteT (DfracOwn 1) (vs ++ u64_le x) }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_lam. wp_pures.
  wp_apply (wp_reserve with "Hs"). clear s. iIntros (s) "[% Hs]". wp_pures.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  wp_apply wp_slice_len. wp_pures.
  wp_apply (wp_SliceTake_full_cap with "Hs").
  { word. }
  iIntros (ex) "[%Hex Hsl]".
  set (s' := slice_take _ _).
  wp_apply wp_SliceSkip.
  { rewrite /slice_take /=. word. }
  iDestruct (slice.own_slice_split_acc s.(Slice.sz) with "Hsl") as "[Hsl Hclose]".
  { len. }
  wp_apply (wp_UInt64Put with "Hsl").
  { len. rewrite Hex. word. }
  iIntros "Hsl". iDestruct ("Hclose" with "Hsl") as "Hsl".
  wp_pures. iApply "HΦ". iModIntro.
  rewrite /own_slice. iExactEq "Hsl". repeat f_equal.
  rewrite /list.untype fmap_app. f_equal.
  { rewrite take_app_length' //. len. }
  rewrite drop_ge //. len. rewrite Hex. word.
Qed.

Theorem wp_WriteBytes s (vs : list u8) data_sl q (data : list u8) :
  {{{ own_slice s byteT (DfracOwn 1) vs ∗ own_slice_small data_sl byteT q data }}}
    WriteBytes (slice_val s) (slice_val data_sl)
  {{{ s', RET slice_val s';
    own_slice s' byteT (DfracOwn 1) (vs ++ data) ∗
    own_slice_small data_sl byteT q data
  }}}.
Proof.
  iIntros (Φ) "[Hs Hdata] HΦ". wp_lam. wp_pures.
  wp_apply (wp_SliceAppendSlice with "[$Hs $Hdata]"); first done.
  iIntros (s') "[Hs' Hdata]".
  iApply ("HΦ" with "[$]").
Qed.

Theorem wp_WriteBool s (vs: list u8) (b: bool) :
  {{{ own_slice s byteT (DfracOwn 1) vs }}}
    WriteBool (slice_val s) #b
  {{{ s', RET (slice_val s');
      own_slice s' byteT (DfracOwn 1) (vs ++ [if b then W8 1 else W8 0]) }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_call.
  destruct b; wp_pures.
  (* TODO: this also breaks through the typed slice library *)
  - wp_apply (wp_SliceAppend' with "Hs"); auto.
    iIntros (s') "Hs".
    iApply "HΦ".
    rewrite /own_slice.
    rewrite list_untype_app //.
  - wp_apply (wp_SliceAppend' with "Hs"); auto.
    iIntros (s') "Hs".
    iApply "HΦ".
    rewrite /own_slice.
    rewrite list_untype_app //.
Qed.

End goose_lang.
