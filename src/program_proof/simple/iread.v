From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import deletable_heap liftable auth_map.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

From Goose.github_com.mit_pdos.goose_nfsd Require Import simple.
From Perennial.program_proof Require Import txn.txn_proof marshal_proof addr_proof crash_lockmap_proof addr.addr_proof buf.buf_proof.
From Perennial.program_proof Require Import buftxn.sep_buftxn_proof.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import NamedProps Map List range_set.
From Perennial.algebra Require Import log_heap.
From Perennial.program_logic Require Import spec_assert.
From Perennial.goose_lang.lib Require Import slice.typed_slice into_val.
From Perennial.program_proof Require Import simple.spec simple.invariant simple.common.

Section heap.
Context `{!buftxnG Σ}.
Context `{!ghost_varG Σ (gmap u64 (list u8))}.
Context `{!mapG Σ u64 (list u8)}.
Implicit Types (stk:stuckness) (E: coPset).

Theorem wp_ReadInode γ γtxn (inum : u64) len blk (btxn : loc) dinit γdurable :
  {{{ is_buftxn_mem Nbuftxn btxn γ.(simple_buftxn) dinit γtxn γdurable ∗
      is_inode_enc inum len blk (buftxn_maps_to γtxn) ∗
      ⌜ inum ∈ covered_inodes ⌝ }}}
    ReadInode #btxn #inum
  {{{ l, RET #l;
      is_buftxn_mem Nbuftxn btxn γ.(simple_buftxn) dinit γtxn γdurable ∗
      is_inode_enc inum len blk (buftxn_maps_to γtxn) ∗
      is_inode_mem l inum len blk }}}.
Proof.
  iIntros (Φ) "(Hbuftxn & Henc & %Hcovered) HΦ".
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
  wp_apply (wp_BufTxn__ReadBuf with "[$Hbuftxn $Hinode_enc_mapsto]"); eauto.
  iIntros (dirty bufptr) "[Hbuf Hbufdone]".

  wp_pures. wp_call.
  wp_apply wp_allocStruct; eauto.
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
  iDestruct (is_dec_to_is_slice_small with "Hdec") as "Hbufslice".
  iMod ("Hbufdone" with "[Hbufslice Hbufwithoutdata] []") as "[Hbuftxn Hbuf]"; eauto.
  {
    iApply is_buf_return_data. iFrame.
    iApply (data_has_obj_to_buf_data with "Hbufslice").
    eauto.
  }
  wp_pures.
  iApply "HΦ".
  iFrame. iExists _. iFrame "∗%".
Qed.

Theorem wp_Inode__Read γ γtxn ip inum len blk (btxn : loc) (offset : u64) (bytesToRead : u64) contents γdurable dinit :
  {{{ is_buftxn_mem Nbuftxn btxn γ.(simple_buftxn) dinit γtxn γdurable ∗
      is_inode_mem ip inum len blk ∗
      is_inode_data len blk contents (buftxn_maps_to γtxn)
  }}}
    Inode__Read #ip #btxn #offset #bytesToRead
  {{{ resSlice (eof : bool) (vs : list u8), RET (slice_val resSlice, #eof);
      is_slice resSlice u8T 1 vs ∗
      is_buftxn_mem Nbuftxn btxn γ.(simple_buftxn) dinit γtxn γdurable ∗
      is_inode_mem ip inum len blk ∗
      is_inode_data len blk contents (buftxn_maps_to γtxn) ∗
      ⌜ firstn (length vs) (skipn (int.nat offset) contents) = vs ⌝ ∗
      ⌜ length vs ≤ int.nat bytesToRead ⌝ ∗
      ⌜ eof = true <-> (int.nat offset + length vs ≥ int.nat len)%nat ⌝
  }}}.
Proof.
  iIntros (Φ) "(Hbuftxn & Hmem & Hdata) HΦ".
  wp_call.
  iNamed "Hmem".
  iNamed "Hdata".
  wp_loadField.
  wp_if_destruct.
  { wp_pures.
    replace (slice.nil) with (slice_val (Slice.nil)); auto.
    iApply "HΦ".
    iSplitR.
    { iApply (is_slice_zero (V:=u8)). }
    iFrame. iSplit.
    { iExists _. iFrame "∗%". }
    iPureIntro; intuition; simpl; lia.
  }

  wp_apply wp_ref_to; first by val_ty.
  iIntros (count) "Hcount".
  wp_loadField. wp_load.

  wp_apply (wp_If_join
    (∃ (countval : u64),
      "Hcount" ∷ count ↦[uint64T] #countval ∗
      "Hisize" ∷ ip ↦[Inode.S :: "Size"] #len ∗
      "%Hcountval0" ∷ ⌜(int.Z countval ≤ int.Z bytesToRead)%Z⌝ ∗
      "%Hcountval1" ∷ ⌜(int.Z offset + int.Z countval ≤ int.Z len)%Z⌝
    ) with "[Hcount Hisize]").
  1: iSplit.
  { iIntros "[%Hdec HΦ]". apply bool_decide_eq_true_1 in Hdec.
    wp_loadField. wp_store.
    iApply "HΦ".
    iExists _. iFrame. iPureIntro. split.
    { lia. }
    word.
  }
  { iIntros "[%Hdec HΦ]". apply bool_decide_eq_false_1 in Hdec.
    wp_pures.
    iApply "HΦ".
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
  wp_apply (wp_BufTxn__ReadBuf with "[$Hbuftxn $Hdiskblk]"); first by reflexivity.

  iIntros (dirty bufptr) "[Hbuf Hbufupd]".
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply wp_ref_to; first by val_ty.
  iIntros (b) "Hb".
  wp_pures.

  replace (replicate (int.nat 0%Z) IntoVal_def) with (@nil u8) by reflexivity.

  wp_apply (wp_forUpto (λ i,
    ∃ dataslice vs,
      "Hdatavar" ∷ datavar ↦[slice.T byteT] (slice_val dataslice) ∗
      "Hdataslice" ∷ is_slice dataslice byteT 1 vs ∗
      "%Hcontent" ∷ ⌜ firstn (int.nat i) (skipn (int.nat offset) contents) = vs ⌝ ∗
      "%Hvslen" ∷ ⌜ length vs = (int.nat i) ⌝ ∗
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

    destruct (vec_to_list bbuf !! int.nat (word.add offset b')) eqn:He.
    2: {
      exfalso.
      eapply lookup_ge_None_1 in He.
      assert (int.nat (word.add offset b') < length contents).
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
    iApply "HΦ'".
    iFrame "Hb".
    iExists _, _.
    iFrame "Hdatavar".
    iFrame "Hdataslice".
    iSplit.
    { iPureIntro. word_cleanup.
      replace (Z.to_nat (int.Z b' + 1)) with (S (int.nat b')) by word.
      erewrite take_S_r.
      { rewrite Hcontent. eauto. }
      rewrite lookup_drop. rewrite -Hdiskdata.
      rewrite lookup_take.
      { replace (int.nat (word.add offset b')) with (int.nat offset + int.nat b') in He by word. done. }
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

  iMod ("Hbufupd" with "[$Hbuf] []") as "[Hbuftxn Hbuf]".
  { intuition. }

  wp_loadField. wp_load. wp_pures.

  wp_apply util_proof.wp_DPrintf.
  wp_load.
  wp_pures.
  iApply "HΦ".
  iFrame "Hdataslice Hbuftxn".
  iFrame. iSplit.
  { iExists _. iFrame "∗%". }

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
