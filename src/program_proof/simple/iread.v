From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import liftable auth_map.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import disk_prelude.

From Goose.github_com.mit_pdos.go_nfsd Require Import simple.
From Perennial.program_proof Require Import obj.obj_proof marshal_proof addr_proof crash_lockmap_proof addr.addr_proof buf.buf_proof.
From Perennial.program_proof Require Import jrnl.sep_jrnl_proof.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import NamedProps Map List range_set.
From Perennial.program_logic Require Import spec_assert.
From Perennial.goose_lang.lib Require Import slice.typed_slice into_val.
From Perennial.program_proof Require Import simple.spec simple.invariant simple.common.

Section heap.
Context `{!heapGS Σ}.
Context `{!simpleG Σ}.
Implicit Types (stk:stuckness) (E: coPset).

Theorem wp_ReadInode γ γtxn (inum : u64) len blk (btxn : loc) dinit γdurable :
  {{{ is_jrnl_mem Njrnl btxn γ.(simple_jrnl) dinit γtxn γdurable ∗
      is_inode_enc inum len blk (jrnl_maps_to γtxn) ∗
      ⌜ inum ∈ covered_inodes ⌝ }}}
    ReadInode #btxn #inum
  {{{ l, RET #l;
      is_jrnl_mem Njrnl btxn γ.(simple_jrnl) dinit γtxn γdurable ∗
      is_inode_enc inum len blk (jrnl_maps_to γtxn) ∗
      is_inode_mem l inum len blk }}}.
Proof.
  iIntros (Φ) "(Hjrnl & Henc & %Hcovered) HΦ".
  iNamed "Henc".

  wp_call.
  wp_apply (wp_inum2Addr); auto.
  {
    iPureIntro.
    rewrite /covered_inodes in Hcovered.
    eapply rangeSet_lookup in Hcovered; try lia.
    rewrite /NumInodes /InodeSz. simpl. lia.
  }

  replace (#(LitInt (word.mul 128 8))) with (#1024%nat) by reflexivity.
  wp_apply (wp_Op__ReadBuf with "[$Hjrnl $Hinode_enc_pointsto]"); eauto.
  iIntros (dirty bufptr) "[Hbuf Hbufdone]".

  wp_pures. wp_call.
  wp_apply wp_allocStruct; first val_ty.
  iIntros (iptr) "Hi".
  iDestruct (struct_fields_split with "Hi") as "Hi". iNamed "Hi".
  wp_apply (wp_buf_loadField_data with "Hbuf").
  iIntros (bufslice) "[Hbufdata Hbufwithoutdata]".
  rewrite is_buf_data_has_obj. iDestruct "Hbufdata" as (bufdata) "[Hbufslice %]".
  wp_apply (wp_new_dec with "Hbufslice").
  { rewrite /encodes_inode in Hinode_encodes.
    rewrite /data_has_obj /= in H. subst. eauto. }
  iIntros (dec) "Hdec".
  wp_storeField.
  wp_apply (wp_Dec__GetInt with "Hdec"). iIntros "Hdec".
  wp_storeField.
  wp_apply (wp_Dec__GetInt with "Hdec"). iIntros "Hdec".
  wp_storeField.
  iDestruct (is_dec_to_own_slice_small with "Hdec") as "Hbufslice".
  iMod ("Hbufdone" with "[Hbufslice Hbufwithoutdata] []") as "[Hjrnl Hbuf]"; eauto.
  {
    iApply is_buf_return_data. iFrame.
    iApply (data_has_obj_to_buf_data with "Hbufslice").
    eauto.
  }
  wp_pures.
  iApply "HΦ".
  by iFrame.
Qed.

Theorem wp_Inode__Read γ γtxn ip inum len blk (btxn : loc) (offset : u64) (bytesToRead : u64) contents γdurable dinit :
  {{{ is_jrnl_mem Njrnl btxn γ.(simple_jrnl) dinit γtxn γdurable ∗
      is_inode_mem ip inum len blk ∗
      is_inode_data len blk contents (jrnl_maps_to γtxn)
  }}}
    Inode__Read #ip #btxn #offset #bytesToRead
  {{{ resSlice (eof : bool) (vs : list u8), RET (slice_val resSlice, #eof);
      own_slice resSlice u8T (DfracOwn 1) vs ∗
      is_jrnl_mem Njrnl btxn γ.(simple_jrnl) dinit γtxn γdurable ∗
      is_inode_mem ip inum len blk ∗
      is_inode_data len blk contents (jrnl_maps_to γtxn) ∗
      ⌜ firstn (length vs) (skipn (uint.nat offset) contents) = vs ⌝ ∗
      ⌜ length vs ≤ uint.nat bytesToRead ⌝ ∗
      ⌜ eof = true <-> (uint.nat offset + length vs ≥ uint.nat len)%nat ⌝
  }}}.
Proof.
  iIntros (Φ) "(Hjrnl & Hmem & Hdata) HΦ".
  wp_call.
  iNamed "Hmem".
  iNamed "Hdata".
  wp_loadField.
  wp_if_destruct.
  { wp_pures.
    replace (slice.nil) with (slice_val (Slice.nil)); auto.
    iApply "HΦ". iModIntro.
    iSplitR.
    { iApply (own_slice_zero (V:=u8)). }
    iFrame. iSplit; first done.
    iPureIntro; intuition; simpl; lia.
  }

  wp_apply wp_ref_to; first by val_ty.
  iIntros (count) "Hcount".
  wp_loadField. wp_load.

  wp_apply (wp_If_join
    (∃ (countval : u64),
      "Hcount" ∷ count ↦[uint64T] #countval ∗
      "Hisize" ∷ ip ↦[Inode :: "Size"] #len ∗
      "%Hcountval0" ∷ ⌜(uint.Z countval ≤ uint.Z bytesToRead)%Z⌝ ∗
      "%Hcountval1" ∷ ⌜(uint.Z offset + uint.Z countval ≤ uint.Z len)%Z⌝
    ) with "[Hcount Hisize]").
  1: iSplit.
  { iIntros "%Hdec". apply bool_decide_eq_true_1 in Hdec.
    wp_loadField. wp_store.
    iSplitR; first done.
    iExists _. iFrame. iPureIntro. split.
    { lia. }
    word.
  }
  { iIntros "%Hdec". apply bool_decide_eq_false_1 in Hdec.
    wp_pures.
    iSplitR; first done.
    iExists _. iFrame. iPureIntro. split.
    { lia. }
    revert Hdec. word.
  }
  iIntros "H". iNamed "H".

  wp_apply util_proof.wp_DPrintf.
  wp_pures.
  wp_apply (wp_NewSlice (V:=u8)).
  iIntros (dataslice) "Hdataslice".
  wp_apply wp_ref_to; first by val_ty.
  iIntros (datavar) "Hdatavar".
  wp_pures.
  wp_loadField.
  wp_apply wp_block2addr.
  wp_apply (wp_Op__ReadBuf with "[$Hjrnl $Hdiskblk]"); first by reflexivity.

  iIntros (dirty bufptr) "[Hbuf Hbufupd]".
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply wp_ref_to; first by val_ty.
  iIntros (b) "Hb".
  wp_pures.

  replace (replicate (uint.nat 0%Z) (IntoVal_def _)) with (@nil u8) by reflexivity.

  wp_apply (wp_forUpto (λ i,
    ∃ dataslice vs,
      "Hdatavar" ∷ datavar ↦[slice.T byteT] (slice_val dataslice) ∗
      "Hdataslice" ∷ own_slice dataslice byteT (DfracOwn 1) vs ∗
      "%Hcontent" ∷ ⌜ firstn (uint.nat i) (skipn (uint.nat offset) contents) = vs ⌝ ∗
      "%Hvslen" ∷ ⌜ length vs = (uint.nat i) ⌝ ∗
      "Hbuf" ∷ is_buf bufptr (blk2addr blk) {|
         bufKind := projT1 (existT KindBlock (bufBlock bbuf));
         bufData := projT2 (existT KindBlock (bufBlock bbuf));
         bufDirty := dirty |}
    )%I with "[] [$Hb Hdatavar Hdataslice Hbuf]").
  { word. }
  {
    iIntros (b').
    iIntros (Φ') "!>".
    iIntros "(HI & Hb & %Hbound) HΦ'".
    iNamed "HI".
    wp_pures.
    wp_load.
    wp_apply (wp_buf_loadField_data with "Hbuf").
    iIntros (vslice) "[Hbufdata Hbufnodata]".
    simpl.
    apply (f_equal length) in Hcontent as Hlens.
    autorewrite with len in Hlens.

    destruct (vec_to_list bbuf !! uint.nat (word.add offset b')) eqn:He.
    2: {
      exfalso.
      eapply lookup_ge_None_1 in He.
      assert (uint.nat (word.add offset b') < length contents).
      { revert Hcountval1. revert Hbound. word. }
      assert (length bbuf ≥ length contents).
      2: { lia. }
      rewrite -Hdiskdata. rewrite take_length. lia.
    }
    wp_apply (wp_SliceGet (V:=u8) with "[$Hbufdata]"); eauto.
    iIntros "Hbufdata".
    wp_load.
    wp_apply (wp_SliceAppend (V:=u8) with "Hdataslice").
    iIntros (dataslice') "Hdataslice".
    wp_store.
    iApply "HΦ'". iModIntro.
    iFrame "Hb".
    iExists _, _.
    iFrame "Hdatavar".
    iFrame "Hdataslice".
    iSplit.
    { iPureIntro. word_cleanup.
      replace (Z.to_nat (uint.Z b' + 1)) with (S (uint.nat b')) by word.
      erewrite take_S_r.
      { rewrite Hcontent. eauto. }
      rewrite lookup_drop. rewrite -Hdiskdata.
      rewrite lookup_take.
      { replace (uint.nat (word.add offset b')) with (uint.nat offset + uint.nat b') in He by word. done. }
      lia.
    }
    iSplit.
    { iPureIntro. rewrite app_length /=. word. }
    iApply is_buf_return_data. iFrame.
  }
  {
    iExists _, _.
    iFrame.
    rewrite /= //.
  }

  iIntros "(HI & Hb)".
  iNamed "HI".

  iMod ("Hbufupd" with "[$Hbuf] []") as "[Hjrnl Hbuf]".
  { intuition. }

  wp_loadField. wp_load. wp_pures.

  wp_apply util_proof.wp_DPrintf.
  wp_load.
  wp_pures.
  iApply "HΦ". iModIntro.
  iFrame "Hdataslice Hjrnl".
  iFrame. iSplit.
  { done. }

  iPureIntro. intuition (try congruence).
  {
    lia.
  }
  {
    apply bool_decide_eq_true_1 in H.
    rewrite Hvslen. revert H. word.
  }
  {
    eapply bool_decide_eq_true_2.
    revert H. rewrite Hvslen. word.
  }
Qed.

End heap.
