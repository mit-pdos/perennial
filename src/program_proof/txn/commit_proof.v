From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From iris.algebra Require Import numbers.

From Perennial.Helpers Require Import Transitions NamedProps Map.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.algebra Require Import deletable_heap log_heap.

From Goose.github_com.mit_pdos.goose_nfsd Require Import txn.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import wal.specs wal.lib wal.heapspec addr.addr_proof buf.buf_proof disk_lib.
From Perennial.program_proof Require Export txn.invariant txn.map_helpers.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Remove Hints fractional.into_sep_fractional : typeclass_instances.

Section goose_lang.
Context `{!txnG Σ}.

Implicit Types (s : Slice.t) (γ: @txn_names Σ).

Record buf_and_prev_data := {
  buf_ : buf;
  data_ : bufDataT buf_.(bufKind);
}.

Definition is_txn_buf_pre γ (bufptr:loc) (a : addr) (buf : buf_and_prev_data) : iProp Σ :=
  "Hisbuf" ∷ is_buf bufptr a buf.(buf_) ∗
  "Hmapto" ∷ mapsto_txn γ a (existT buf.(buf_).(bufKind) buf.(data_)).

Definition is_txn_buf_blkno (bufptr : loc) (a : addr) (buf : buf) blkno :=
  ( "Hisbuf" ∷ is_buf bufptr a buf ∗
    "%HaddrBlock" ∷ ⌜a.(addrBlock) = blkno⌝ )%I.

Definition updOffsetsOK blknum diskLatest walBlock K (offmap : gmap u64 buf) : Prop :=
  ∀ off (oldBufData : @bufDataT K),
    valid_addr (Build_addr blknum off) ->
    valid_off K off ->
    is_bufData_at_off diskLatest off oldBufData ->
    match offmap !! off with
    | None => is_bufData_at_off walBlock off oldBufData
    | Some buf => is_bufData_at_off walBlock off buf.(bufData) ∧
      buf.(bufKind) = K
    end.

Definition updBlockOK blknum walBlock K (locked_wh_disk : disk) (offmap : gmap u64 buf) : Prop :=
  ∀ diskLatest,
    locked_wh_disk !! int.val blknum = Some diskLatest ->
    updOffsetsOK blknum diskLatest walBlock K offmap.

Definition updBlockKindOK blknum walBlock γ (locked_wh_disk : disk) (offmap : gmap u64 buf) : Prop :=
  ∃ K,
    γ.(txn_kinds) !! blknum = Some K ∧
    updBlockOK blknum walBlock K locked_wh_disk offmap.

Lemma valid_off_block blknum off :
  valid_addr (Build_addr blknum off) ->
  valid_off KindBlock off ->
  off = 0.
Proof.
  rewrite /valid_addr /valid_off /bufSz /addr2flat_z; intuition idtac.
  simpl addrOff in *.
  simpl addrBlock in *.
  cut (int.val off = 0); [intros; word|].
  apply Z.div_exact in H0 as ->; [|word].
  rewrite Z.div_small; [|word].
  reflexivity.
Qed.

Theorem mapsto_txn_locked (γ : txn_names) l dinit lwh a data E :
  ↑invN ⊆ E ->
  ↑walN ⊆ E ∖ ↑invN ->
  is_wal (wal_heap_inv γ.(txn_walnames)) l (wal_heap_walnames γ.(txn_walnames)) dinit ∗
  inv invN (is_txn_always γ) ∗
  is_locked_walheap γ.(txn_walnames) lwh ∗
  mapsto_txn γ a data
  ={E}=∗
    is_locked_walheap γ.(txn_walnames) lwh ∗
    mapsto_txn γ a data ∗
    ⌜ ∃ v, locked_wh_disk lwh !! int.val a.(addrBlock) = Some v ⌝.
Proof.
  iIntros (H0 H1) "(#Hiswal & #Hinv & Hlockedheap & Hmapsto)".
  iInv "Hinv" as ">Htxnalways".
  iNamed "Htxnalways".
  iNamed "Hmapsto".
  iDestruct (gen_heap_valid with "Hmetactx Hmapsto_meta") as %Hvalid.
  eapply gmap_addr_by_block_lookup in Hvalid.
  destruct Hvalid as [offmap [Hmetam Hoffmap]].
  iDestruct (big_sepM2_lookup_2_some with "Hheapmatch") as (x) "%Hlm"; eauto.
  iDestruct (big_sepM2_lookup_acc with "Hheapmatch") as "[Hx Hheapmatch]"; eauto.
  iNamed "Hx".
  iMod (wal_heap_mapsto_latest with "[$Hiswal $Hlockedheap $Htxn_hb]") as "(Hlockedheap & Htxn_hb & %)"; eauto.
  iModIntro.
  iSplitR "Hlockedheap Hmapsto_log Hmapsto_meta Hmod_frag".
  { iNext. iExists _, _, _. iFrame.
    iApply "Hheapmatch". iExists _, _, _. iFrame. iFrame "%". }
  iModIntro.
  iFrame.
  iSplitL.
  { iExists _. iFrame. }
  iExists _. done.
Qed.

Theorem wp_txn__installBufsMap l q walptr γ dinit lwh bufs buflist (bufamap : gmap addr buf_and_prev_data) :
  {{{ inv invN (is_txn_always γ) ∗
      is_wal (wal_heap_inv γ.(txn_walnames)) walptr (wal_heap_walnames γ.(txn_walnames)) dinit ∗
      readonly (l ↦[Txn.S :: "log"] #walptr) ∗
      is_locked_walheap γ.(txn_walnames) lwh ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist,
        is_txn_buf_pre γ bufptrval a buf
  }}}
    Txn__installBufsMap #l (slice_val bufs)
  {{{ (blkmapref : loc) (blkmap : Map.t Slice.t), RET #blkmapref;
      is_locked_walheap γ.(txn_walnames) lwh ∗
      is_map blkmapref blkmap ∗
      ( [∗ map] a ↦ buf ∈ bufamap,
        mapsto_txn γ a (existT buf.(buf_).(bufKind) buf.(data_)) ) ∗
      [∗ map] blkno ↦ blkslice; offmap ∈ blkmap; gmap_addr_by_block bufamap,
        ∃ b,
          is_block blkslice 1 b ∗
          ⌜ updBlockKindOK blkno b γ (locked_wh_disk lwh) (buf_ <$> offmap) ⌝
  }}}.
Proof using txnG0 txnG0 Σ.
  iIntros (Φ) "(#Hinv & #Hiswal & #log & Hlockedheap & Hbufs & Hbufpre) HΦ".

Opaque struct.t.
  wp_call.
  wp_apply wp_NewMap.
  iIntros (blks) "Hblks".

  iDestruct (is_slice_to_small with "Hbufs") as "Hbufs".
  wp_apply (wp_forSlicePrefix
      (fun done todo =>
        ∃ bufamap_todo bufamap_done blkmap,
        "<-" ∷ ⌜ done ++ todo = buflist ⌝ ∗
        "->" ∷ ⌜ bufamap_done = bufamap ∖ bufamap_todo ⌝ ∗
        "%" ∷ ⌜ bufamap_todo ⊆ bufamap ⌝ ∗
        "Hblks" ∷ is_map blks blkmap ∗
        "Hbufamap_todo" ∷ ( [∗ maplist] a↦buf;bufptrval ∈ bufamap_todo;todo, is_txn_buf_pre γ bufptrval a buf ) ∗
        "Hbufamap_done" ∷ ( [∗ map] blkno ↦ blkslice; offmap ∈ blkmap; gmap_addr_by_block bufamap_done,
          ∃ b,
            is_block blkslice 1 b ∗
            ⌜ updBlockKindOK blkno b γ (locked_wh_disk lwh) (buf_ <$> offmap) ⌝ ) ∗
        "Hbufamap_done_mapsto" ∷ ( [∗ map] a↦buf ∈ bufamap_done, mapsto_txn γ a (existT buf.(buf_).(bufKind) buf.(data_)) ) ∗
        "Hlockedheap" ∷ is_locked_walheap γ.(txn_walnames) lwh
      )%I
      with "[] [$Hbufs Hbufpre Hblks Hlockedheap]").
  2: {
    iExists bufamap, ∅, ∅.
    iSplitR; try done.
    iSplitR.
    { iPureIntro. rewrite map_difference_diag. done. }
    iFrame "Hblks". iFrame "Hbufpre". iFrame "Hlockedheap".
    iSplitR.
    { iPureIntro. set_solver. }
    iSplit.
    { rewrite gmap_addr_by_block_empty. iApply big_sepM2_empty. done. }
    iApply big_sepM_empty. done.
  }
  {
    iIntros (i b ? ? Hdonetodo).
    iIntros (Φ') "!> HP HΦ'".
    iNamed "HP".

    iDestruct (big_sepML_delete_cons with "Hbufamap_todo") as (a buf) "(%Hb & Htxnbuf & Hbufamap_todo)".
    iNamed "Htxnbuf".

    iMod (mapsto_txn_locked with "[$Hiswal $Hinv $Hmapto $Hlockedheap]") as "(Hlockedheap & Hmapto & %Hlockedsome)".
    1: solve_ndisj.
    1: solve_ndisj.
    destruct Hlockedsome as [lockedv Hlockedsome].

    wp_pures.
    wp_apply (wp_buf_loadField_sz with "Hisbuf"). iIntros "Hisbuf".
    destruct (decide (buf.(buf_).(bufKind) = KindBlock)).

    - replace (bufSz buf.(buf_).(bufKind)) with (bufSz KindBlock) by congruence.
      Opaque BlockSize. Opaque bufSz.
      wp_pures.

      iMod (mapsto_txn_valid with "Hinv Hmapto") as "[Hmapto %Hvalid]".
      { solve_ndisj. }

      intros.

      wp_apply (wp_buf_loadField_data with "Hisbuf"). iIntros (bufdata) "[Hbufdata Hisbuf_wd]".
      wp_apply (wp_buf_wd_loadField_addr with "Hisbuf_wd"). iIntros "Hisbuf_wd".

      wp_apply (wp_MapInsert with "Hblks").
      { reflexivity. }
      iIntros "Hblks".

      iApply "HΦ'".
      iExists (delete a bufamap_todo), (<[a := buf]> (bufamap ∖ bufamap_todo)), _.
      iSplitR.
      { rewrite -app_assoc. simpl. done. }
      iSplitR.
      { iPureIntro. erewrite map_difference_delete; eauto.
        eapply lookup_weaken; eauto. }
      iFrame "Hblks".
      iFrame "Hbufamap_todo".

      iFrame "Hlockedheap".
      iSplitR.
      { iPureIntro. etransitivity; first by apply delete_subseteq. eauto. }
      iSplitR "Hbufamap_done_mapsto Hmapto".
      2: {
        iApply (big_sepM_insert_2 with "[Hmapto] Hbufamap_done_mapsto").
        intuition.
      }
      rewrite /map_insert.
      rewrite gmap_addr_by_block_insert.
      2: { eapply lookup_difference_None; eauto. }
      iApply (big_sepM2_insert_2 with "[Hbufdata] Hbufamap_done").
      simpl.
      rewrite /is_buf_data /is_block.

      destruct buf. destruct buf_0. simpl in *.
      destruct bufData; try congruence.

      iExists _. iFrame. iPureIntro.
      eexists _. intuition eauto.
      intro diskLatest; intros.
      intro off; intros.

      destruct a.
      eapply valid_off_block in H2; eauto.
      eapply valid_off_block in H5; eauto.
      rewrite H2. rewrite H5.
      rewrite lookup_fmap.
      rewrite lookup_insert.
      simpl. done.

    - wp_pures.
      wp_if_destruct.
      {
        exfalso.
        destruct buf; destruct buf_0; simpl in *.
        destruct bufKind; cbn in *; try congruence.
        { inversion H1. }
        { inversion H1. }
      }

      wp_apply wp_ref_of_zero; first by eauto.
      iIntros (blkvar) "Hblkvar".

      wp_apply (wp_buf_loadField_addr with "Hisbuf"). iIntros "Hisbuf".
      wp_apply (wp_MapGet with "Hblks"). iIntros (v ok) "[% Hblks]".
      wp_pures.

      iMod (mapsto_txn_valid with "Hinv Hmapto") as "[Hmapto %Hvalid]".
      { solve_ndisj. }

      wp_apply (wp_If_join
        ( ∃ blkslice blk blkmap',
            "Hblkvar" ∷ blkvar ↦[slice.T byteT] (slice_val blkslice) ∗
            "Hisblock" ∷ is_block blkslice 1 blk ∗
            "Hbufamap_done" ∷ ( [∗ map] blkno↦blkslice;offmap ∈ delete a.(addrBlock) blkmap';
                  delete a.(addrBlock) (gmap_addr_by_block (bufamap ∖ bufamap_todo)),
                  ∃ b0 : Block,
                    is_block blkslice 1 b0
                    ∗ ⌜updBlockKindOK blkno b0 γ
                         (locked_wh_disk lwh) (buf_ <$> offmap)⌝ ) ∗
            "Hisbuf" ∷ is_buf b a buf.(buf_) ∗
            "Hlockedheap" ∷ is_locked_walheap γ.(txn_walnames) lwh ∗
            "Hblks" ∷ is_map blks blkmap' ∗
            "%" ∷ ⌜ blkmap' !! a.(addrBlock) = Some blkslice ⌝ ∗
            "%" ∷ ⌜ updBlockOK a.(addrBlock) blk buf.(buf_).(bufKind) (locked_wh_disk lwh) (default ∅ ((gmap_addr_by_block (buf_ <$> (bufamap ∖ bufamap_todo))) !! a.(addrBlock))) ⌝
        )%I
        with "[Hbufamap_done Hisbuf Hblkvar Hlockedheap Hblks]"); first iSplit.
      {
        iIntros "(-> & HΦ)".
        wp_store.
        apply map_get_true in H0.
        iDestruct (big_sepM2_lookup_1_some with "Hbufamap_done") as (xx) "%Hx"; eauto.
        iDestruct (big_sepM2_delete with "Hbufamap_done") as "[Ha Hbufamap_done]"; eauto.
        iDestruct "Ha" as (b0) "[Hisblock %]".
        iApply "HΦ".
        iExists _, _, _. iFrame.
        iSplit; first by done.
        iPureIntro.
        rewrite gmap_addr_by_block_fmap.
        rewrite lookup_fmap.
        rewrite Hx. simpl.
        destruct H1. destruct H1. intuition idtac.
        rewrite H1 in H6. inversion H6; clear H6; subst. eauto.
      }
      {
        iIntros "(-> & HΦ)".
        wp_apply (wp_buf_loadField_addr with "Hisbuf"). iIntros "Hisbuf".
        wp_loadField.
        wp_apply (wp_Walog__Read with "[$Hiswal $Hlockedheap]"); eauto.
        iIntros (s) "[Hlockedheap Hisblock]".
        wp_store.
        wp_load.
        wp_apply (wp_buf_loadField_addr with "Hisbuf"). iIntros "Hisbuf".
        wp_apply (wp_MapInsert with "[$Hblks]").
        { reflexivity. }
        iIntros "Hblks".
        iApply "HΦ".
        iExists _, _, _. iFrame.

        apply map_get_false in H0; destruct H0; subst.
        iDestruct (big_sepM2_lookup_1_none with "Hbufamap_done") as %Hnone; eauto.

        rewrite delete_insert_delete.
        rewrite delete_notin; eauto.
        rewrite /map_insert lookup_insert delete_notin; eauto.
        iFrame "Hbufamap_done".
        iSplit; first by done.
        iPureIntro.
        rewrite gmap_addr_by_block_fmap.
        rewrite lookup_fmap.

        rewrite Hnone.
        intro diskLatest; intros.
        intro off; intros.
        rewrite lookup_empty; intros.
        congruence.
      }

      iIntros "H". iNamed "H".

      wp_pures.
      wp_load.
      wp_apply (wp_Buf__Install with "[$Hisbuf $Hisblock]").
      iIntros (blk') "(Hisbuf & His_block & %Hinstall_ok)".

      iApply "HΦ'".
      iExists (delete a bufamap_todo), (<[a := buf]> (bufamap ∖ bufamap_todo)), _.
      iFrame "Hblks Hlockedheap Hbufamap_todo".
      iSplitR.
      { rewrite -app_assoc. done. }
      iSplitR.
      { iPureIntro. erewrite map_difference_delete; eauto.
        erewrite lookup_weaken; eauto. }
      iSplitR.
      { iPureIntro. etransitivity; first by apply delete_subseteq. eauto. }
      iSplitR "Hbufamap_done_mapsto Hmapto".
      2: {
        iApply (big_sepM_insert_2 with "[Hmapto] [$Hbufamap_done_mapsto]").
        iFrame. }
      rewrite gmap_addr_by_block_insert.
      2: { eapply lookup_difference_None; eauto. }
      replace (blkmap') with (<[a.(addrBlock) := blkslice]> blkmap') at 2.
      2: { rewrite insert_id; eauto. }
      iApply big_sepM2_insert_delete.
      iFrame "Hbufamap_done".
      iExists _. iFrame. iPureIntro.

      eexists _. intuition eauto.
      intro diskLatest; intros.
      intro off; intros.
      specialize (H2 diskLatest H4 off oldBufData H7 H8 H9).
      destruct (decide (a.(addrOff) = off)).
      + subst.
        rewrite lookup_fmap.
        rewrite lookup_insert. simpl.
        specialize (Hinstall_ok a.(addrOff)).
        destruct (decide (a.(addrOff) = a.(addrOff))); try congruence.
        destruct (default ∅ ((gmap_addr_by_block (buf_ <$> bufamap ∖ bufamap_todo)) !!
                    a.(addrBlock)) !! a.(addrOff)); eauto.
        intuition eauto.
        destruct b0; simpl in *.
        subst. eauto.

      + rewrite lookup_fmap. rewrite lookup_insert_ne; eauto.
        specialize (Hinstall_ok off).
        destruct (decide (off = a.(addrOff))); try congruence.
        rewrite gmap_addr_by_block_fmap in H2.
        rewrite lookup_fmap in H2.
        rewrite default_fmap in H2.
        rewrite lookup_fmap in H2.

        destruct (default ∅ ((gmap_addr_by_block (bufamap ∖ bufamap_todo)) !!
                    a.(addrBlock)) !! off); simpl in *; eauto.
        destruct b0. destruct buf_0. simpl in *. intuition subst.
        eauto.
  }

  iIntros "[Hbufs H]". iNamed "H".
  wp_pures.

  iDestruct (big_sepML_empty_m with "Hbufamap_todo") as "%Hbufamap_todo_empty"; subst.
  rewrite map_difference_empty.
  iApply "HΦ". iFrame.
Qed.

Theorem wp_MkBlockData blkno dataslice :
  {{{
    emp
  }}}
    MkBlockData #blkno (slice_val dataslice)
  {{{
    RET (update_val (blkno, dataslice)%core);
    emp
  }}}.
Proof.
  iIntros (Φ) "Hisblock HΦ".
  wp_call.
  rewrite /update_val.
  iApply "HΦ".
  done.
Qed.

Theorem wp_txn__installBufs l q walptr γ dinit lwh bufs buflist (bufamap : gmap addr buf_and_prev_data) :
  {{{ inv invN (is_txn_always γ) ∗
      is_wal (wal_heap_inv γ.(txn_walnames)) walptr (wal_heap_walnames γ.(txn_walnames)) dinit ∗
      readonly (l ↦[Txn.S :: "log"] #walptr) ∗
      is_locked_walheap γ.(txn_walnames) lwh ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist,
        is_txn_buf_pre γ bufptrval a buf
  }}}
    Txn__installBufs #l (slice_val bufs)
  {{{ (blkslice : Slice.t) upds, RET (slice_val blkslice);
      is_locked_walheap γ.(txn_walnames) lwh ∗
      updates_slice blkslice upds ∗
      ( [∗ map] a ↦ buf ∈ bufamap,
        mapsto_txn γ a (existT buf.(buf_).(bufKind) buf.(data_)) ) ∗
      [∗ maplist] blkno ↦ offmap; upd ∈ gmap_addr_by_block bufamap; upds,
        ⌜ upd.(update.addr) = blkno ⌝ ∗
        ⌜ updBlockKindOK blkno upd.(update.b) γ (locked_wh_disk lwh) (buf_ <$> offmap) ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hinv & #Hiswal & #Hlog & Hlockedheap & Hbufs & Hbufpre) HΦ".

  wp_call.
  wp_apply wp_ref_of_zero; first by eauto.
  iIntros (blks_var) "Hblks_var".

  wp_apply (wp_txn__installBufsMap with "[$Hinv $Hiswal $Hlog $Hlockedheap $Hbufs $Hbufpre]").
  iIntros (blkmapref blkmap) "(Hlockedheap & Hblkmapref & Hbufamap_mapsto & Hblkmap)".

  wp_apply (wp_MapIter_2 _ _ _ _
    (λ mtodo mdone,
      ∃ (blks : Slice.t) upds offmaps_todo offmaps_done,
        "Hblks_var" ∷ blks_var ↦[slice.T (struct.t Update.S)] (slice_val blks) ∗
        "Hblks" ∷ updates_slice blks upds ∗
        "%" ∷ ⌜ gmap_addr_by_block bufamap = offmaps_todo ∪ offmaps_done ⌝ ∗
        "%" ∷ ⌜ dom (gset u64) offmaps_todo ## dom (gset u64) offmaps_done ⌝ ∗
        "Hmtodo" ∷ ( [∗ map] blkno↦blkslice;offmap ∈ mtodo;offmaps_todo, ∃ b : Block,
                                          is_block blkslice 1 b ∗
                                          ⌜ updBlockKindOK blkno b γ (locked_wh_disk lwh) (buf_ <$> offmap) ⌝ ) ∗
        "Hmdone" ∷ ( [∗ maplist] blkno↦offmap;upd ∈ offmaps_done;upds,
                                          ⌜ upd.(update.addr) = blkno ⌝ ∗
                                          ⌜ updBlockKindOK blkno upd.(update.b) γ (locked_wh_disk lwh) (buf_ <$> offmap) ⌝ )
    )%I with "Hblkmapref [Hblks_var Hblkmap]").
  {
    rewrite zero_slice_val.
    iExists _, nil, _, ∅.
    iFrame "Hblks_var".
    iFrame "Hblkmap".
    iSplitL.
    { rewrite /updates_slice. iExists nil. simpl.
      iSplitL; last by done.
      iApply is_slice_zero.
    }
    iSplitL.
    { iPureIntro. rewrite right_id. done. }
    iSplitL.
    { iPureIntro. rewrite dom_empty. set_solver. }
    iApply big_sepML_empty.
  }
  {
    iIntros (k v mtodo mdone).
    iIntros (Φ') "!> [HI %] HΦ'".
    iNamed "HI".

    iDestruct (big_sepM2_lookup_1_some with "Hmtodo") as (x) "%Hx"; eauto.
    iDestruct (big_sepM2_delete with "Hmtodo") as "[Htodo Hmtodo]"; eauto.
    iDestruct "Htodo" as (b) "[Hisblock %]".

    wp_apply (wp_MkBlockData with "[$]"). iIntros "_".
    wp_load.
    wp_apply (wp_SliceAppend_updates with "[Hblks Hisblock]").
    { iFrame. }
    iIntros (blks') "Hblks'".
    wp_store.
    iApply "HΦ'".

    iExists _, _, (delete k offmaps_todo), (<[k := x]> offmaps_done).
    iFrame "Hblks_var Hblks' Hmtodo".
    iSplitR.
    { iPureIntro. rewrite H0. rewrite delete_insert_union; eauto. }
    iSplitR.
    { iPureIntro. set_solver. }
    iApply big_sepML_insert_app.
    { eapply (not_elem_of_dom (D:=gset u64)).
      assert (k ∈ dom (gset u64) offmaps_todo).
      { eapply elem_of_dom; eauto. }
      set_solver. }
    iFrame "Hmdone".
    simpl. done.
  }

  iIntros "[Hblkmapref H]".
  iNamed "H".
  wp_load.
  iDestruct (big_sepM2_empty_r with "Hmtodo") as "->".
  rewrite left_id in H. subst.
  iApply "HΦ".
  iFrame.
Qed.

Theorem bi_iff_1 {PROP:bi} (P Q: PROP) :
  P ≡ Q ->
  ⊢ P -∗ Q.
Proof.
  intros ->; auto.
Qed.

Theorem bi_iff_2 {PROP:bi} (P Q: PROP) :
  P ≡ Q ->
  ⊢ Q -∗ P.
Proof.
  intros ->; auto.
Qed.

Theorem wp_txn__doCommit l q γ dinit bufs buflist bufamap E (Q : nat -> iProp Σ) :
  {{{ is_txn l γ dinit ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      ( [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist, is_txn_buf_pre γ bufptrval a buf ) ∗
      ( |={⊤ ∖ ↑walN ∖ ↑invN, E}=> ∃ (σl : async (gmap addr {K & bufDataT K})),
          "Hcrashstates_frag" ∷ ghost_var γ.(txn_crashstates) (1/2) σl ∗
          "Hcrashstates_fupd" ∷ (
            let σ := ((λ b, existT b.(buf_).(bufKind) b.(buf_).(bufData)) <$> bufamap) ∪ latest σl in
            ghost_var γ.(txn_crashstates) (1/2) (async_put σ σl)
            ={E, ⊤ ∖ ↑walN ∖ ↑invN}=∗ Q (length (possible σl)) ) )
  }}}
    Txn__doCommit #l (slice_val bufs)
  {{{ (commitpos : u64) (ok : bool), RET (#commitpos, #ok);
      if ok then
        ∃ txn_id,
        txn_pos (wal_heap_walnames (txn_walnames γ)) txn_id commitpos ∗ Q txn_id ∗
        [∗ map] a ↦ buf ∈ bufamap,
          mapsto_txn γ a (existT _ buf.(buf_).(bufData))
      else
        [∗ map] a ↦ buf ∈ bufamap,
          mapsto_txn γ a (existT buf.(buf_).(bufKind) buf.(data_))
  }}}.
Proof using txnG0 Σ.
  iIntros (Φ) "(#Htxn & Hbufs & Hbufpre & Hfupd) HΦ".
  iPoseProof "Htxn" as "Htxn0".
  iNamed "Htxn".

  wp_call.
  wp_loadField.
  wp_apply acquire_spec; eauto.
  iIntros "[Hlocked Htxnlocked]".

  wp_pures.
  iNamed "Htxnlocked".

  wp_apply (wp_txn__installBufs with "[$Histxna $Hiswal $Histxn_wal $Hbufs $Hbufpre $Hwal_latest]").
  iIntros (blks updlist) "(Hwal_latest & Hblks & Hmapstos & #Hupdmap)".
  wp_pures.
  wp_apply util_proof.wp_DPrintf.
  wp_loadField.

  wp_apply (wp_Walog__MemAppend _
    ("Hlockedheap" ∷ is_locked_walheap γ.(txn_walnames) lwh ∗
     "Hmapstos" ∷ [∗ map] a↦buf ∈ bufamap, mapsto_txn γ a (existT _ buf.(data_)))
    (λ npos,
      ∃ lwh' txn_id,
        "Hlockedheap" ∷ is_locked_walheap γ.(txn_walnames) lwh' ∗
        "Hmapstos" ∷ ( [∗ map] k↦x ∈ bufamap, mapsto_txn γ k (existT _ x.(buf_).(bufData)) ) ∗
        "Hpos" ∷ txn_pos (wal_heap_walnames (txn_walnames γ)) txn_id npos ∗
        "HQ" ∷ Q txn_id
    )%I
    with "[$Hiswal $Hblks Hmapstos Hwal_latest Hfupd]").
  { iApply (wal_heap_memappend E with "[Hfupd] Hwal_latest Hmapstos").
    iIntros "Hmapstos".
    iInv invN as ">Hinner" "Hinner_close".
    iMod "Hfupd".
    iModIntro.
    iNamed "Hinner".
    iNamed "Hfupd".

    rewrite /memappend_pre.
    rewrite /memappend_crash_pre.

    iDestruct (ghost_var_agree with "Hcrashstates Hcrashstates_frag") as %->.

    iDestruct (gmap_addr_by_block_big_sepM with "Hmapstos") as "Hmapstos".

    iAssert (⌜ ∀ a, a ∈ dom (gset _) (gmap_addr_by_block bufamap) -> a ∈ dom (gset _) (gmap_addr_by_block σl.(latest)) ⌝)%I as "%Hsubset".
    {
      iIntros (a Ha).
      apply lookup_lookup_total_dom in Ha.
      remember (gmap_addr_by_block bufamap !!! a) as x.
      iDestruct (big_sepM_lookup with "Hmapstos") as "Ha"; eauto.
      eapply gmap_addr_by_block_off_not_empty in Ha as Hx.
      assert (x = (list_to_map (map_to_list x) : gmap u64 _)) as Hlm. { rewrite list_to_map_to_list; eauto. }
      rewrite -> Hlm in *.
      destruct (map_to_list x) eqn:Hxl.
      { simpl in Hx. congruence. }
      simpl.
      iDestruct (big_sepM_lookup_acc with "Ha") as "[H Ha]".
      { apply lookup_insert. }
      iNamed "H".
      iDestruct (log_heap_valid_cur with "Hlogheapctx Hmapsto_log") as %Hvalid.
      eapply gmap_addr_by_block_lookup in Hvalid as Hvalidblock; destruct Hvalidblock; intuition idtac.
      iPureIntro.
      apply elem_of_dom. rewrite H0. eauto.
    }
    apply elem_of_subseteq in Hsubset.

    iDestruct (big_sepML_sep with "Hupdmap") as "[Hupdmap_addr Hupdmap_kind]".

    iDestruct (big_sepML_change_m _
      (filter (λ (k : u64 * _), fst k ∈ dom (gset u64) (gmap_addr_by_block bufamap)) (gmap_addr_by_block σl.(latest)))
      with "Hupdmap_addr") as "Hupdmap_addr_2".
    { symmetry. apply dom_filter_L. intros i; split.
      { intros H. apply Hsubset in H as H'.
        apply elem_of_dom in H'. destruct H'. eexists; split; eauto. }
      { intros H. destruct H as [x H]. intuition. }
    }

    iDestruct (big_sepM2_dom with "Hheapmatch") as "%Hheapmatch_dom".
    iDestruct (big_sepM2_sepM_1 with "Hheapmatch") as "Hheapmatch".
    iDestruct (big_sepM_filter_split with "Hheapmatch") as "[Hheapmatch Hheapmatch_rebuild]".

    iDestruct (bi_iff_2 with "[Hupdmap_addr_2 Hheapmatch]") as "Hheapmatch".
    1: eapply big_sepML_sepM.
    1: iFrame "Hupdmap_addr_2 Hheapmatch".

    iDestruct (big_sepML_mono _
      (λ k (v : gmap u64 {K & bufDataT K}) lv,
        ∃ (installed_bs : Block * list Block),
          ( ∃ blockK v0,
            ⌜lv.(update.addr) = k⌝ ∗
            ⌜gmap_addr_by_block metam !! lv.(update.addr) = Some v0⌝ ∗
            ⌜γ.(txn_kinds) !! lv.(update.addr) = Some blockK⌝ ∗
            bufDataTs_in_block (fst installed_bs) (snd installed_bs) lv.(update.addr) blockK v v0 ) ∗
          mapsto lv.(update.addr) 1 (HB (fst installed_bs) (snd installed_bs))
      )%I with "Hheapmatch []") as "Hheapmatch".
    {
      iIntros (k v lv). iPureIntro.
      iIntros "(<- & H)".
      iDestruct "H" as (v0) "(% & H)".
      iDestruct "H" as (installed bs blockK) "(% & H0 & H1)".
      iExists (installed, bs). iFrame.
      iExists _, _. iFrame. done. }

    iDestruct (big_sepML_exists with "Hheapmatch") as (updlist_olds) "[-> Hheapmatch]".
    iExists (snd <$> updlist_olds).
    iExists crash_heaps.

    iFrame "Hcrashheaps".

    iDestruct (big_sepML_sepL_split with "Hheapmatch") as "[Hheapmatch Hupdlist_olds]".

    iSplitL "Hupdlist_olds".
    {
      iApply big_sepL2_alt.
      iSplitR.
      { repeat rewrite fmap_length. eauto. }
      rewrite zip_fst_snd. iFrame.
    }

    iIntros (pos' lwh') "(Hcrash & Hq)".
    rewrite /memappend_crash /memappend_q.

    iDestruct "Hcrash" as "(Hlockedheap & Hcrashheaps)".
    rewrite (big_sepL2_alt _ updlist_olds.*1).
    iDestruct "Hq" as "[_ Hq]".
    rewrite zip_fst_snd.

    remember (((λ b, existT _ b.(buf_).(bufData)) <$> bufamap) ∪ σl.(latest)) as σl'latest.

    pose proof (filter_union_gmap_addr_by_block_ignored σl.(latest)
                  ((λ b, existT _ b.(buf_).(bufData)) <$> bufamap)
                  (λ x, x ∉ dom (gset u64) (gmap_addr_by_block bufamap))) as Hy.
    rewrite Hy.
    2: {
      intros k a Hka.
      rewrite lookup_fmap in Hka. apply fmap_Some_1 in Hka. destruct Hka. intuition. apply H0; clear H0.
      eapply gmap_addr_by_block_lookup in H1. destruct H1. intuition.
      apply elem_of_dom. eauto.
    }

    iDestruct (big_sepML_sepL_combine with "[$Hheapmatch $Hq]") as "Hheapmatch".
    iDestruct (big_sepML_sepM_ex with "Hheapmatch") as "Hheapmatch".
    iDestruct (big_sepM_mono_dom with "[] Hheapmatch") as "Hheapmatch".
    3: iDestruct (big_sepM_filter_split with "[$Hheapmatch $Hheapmatch_rebuild]") as "Hheapmatch".
    { simpl. epose proof (dom_filter_eq (gmap_addr_by_block σl.(latest)) _ (λ x, x ∈ dom (gset u64) (gmap_addr_by_block bufamap))) as He.
      rewrite He. 1: reflexivity.
      rewrite gmap_addr_by_block_dom_union.
      rewrite gmap_addr_by_block_fmap. rewrite dom_fmap_L. set_solver. }
    { simpl. iModIntro. iIntros (k offmap Hoffmap) "H".
      iDestruct "H" as (lv) "[H Hmapsto]".
      iDestruct "H" as (blockK meta) "(% & % & % & Hinblock)".
      eapply map_filter_lookup_Some_12 in Hoffmap as Hbufamap_in.
      eapply elem_of_dom in Hbufamap_in. destruct Hbufamap_in as [offmap' Hbufamap_in].
      iExists (((λ b, existT b.(buf_).(bufKind) b.(buf_).(bufData)) <$> offmap') ∪ offmap).
      iSplit.
      { iPureIntro. eapply map_filter_lookup_Some_2.
        2: { simpl. eapply elem_of_dom. eauto. }
        admit. }
      subst.
      iExists _. iSplit; eauto.
      iExists _, _, _. iSplit; eauto.
      iFrame "Hmapsto".
      admit.
    }

    iDestruct (gmap_addr_by_block_big_sepM' _
      (λ a v, mapsto_txn γ a (existT v.(buf_).(bufKind) v.(data_)))
      with "Hmapstos") as "Hmapstos".

    iDestruct (big_sepL2_length with "Hcrashheapsmatch") as "%Hcrash_heaps_len".

    iCombine ("Hcrashstates_frag Hcrashstates") as "Hcrashstates".
    iMod (ghost_var_update (async_put σl'latest σl) with "Hcrashstates") as "[Hcrashstates Hcrashstates_frag]".

    iDestruct (mapsto_txn_cur_map _ _ _
      (λ b, Build_buf_and_prev_data (b.(buf_)) (b.(buf_).(bufData)))
      with "Hmapstos") as "[Hmapsto_cur Hmapstos]".
    iMod (log_heap_append _ (((λ b : buf_and_prev_data, existT b.(buf_).(bufKind) b.(buf_).(bufData)) <$> bufamap)) with "Hlogheapctx [Hmapsto_cur]") as "[Hlogheapctx Hnewmapsto]".
    { iApply (big_sepM_mono_dom with "[] Hmapsto_cur").
      { rewrite dom_fmap_L. done. }
      iModIntro. iIntros (k x Hkx) "Hmapsto_cur".
      iExists _. rewrite lookup_fmap Hkx /=. iSplit; first by done.
      iExists _. iFrame. }
    iDestruct ("Hmapstos" with "[Hnewmapsto]") as "Hmapstos".
    { rewrite ?big_sepM_fmap /=. iFrame. }

    iMod ("Hcrashstates_fupd" with "Hcrashstates_frag") as "HQ".

    iMod ("Hinner_close" with "[-HQ Hlockedheap Hmapstos]") as "Hinner_close".
    { iNext.
      iExists _, _, _. iFrame.
      iSplitL "Hcrashstates". { subst. iFrame. }
      simpl.
      iSplitL "Hheapmatch".
      { iApply (big_sepM_sepM2_merge_ex with "Hheapmatch").
        rewrite -Hheapmatch_dom.
        rewrite gmap_addr_by_block_dom_union.
        rewrite gmap_addr_by_block_fmap. rewrite dom_fmap_L. set_solver. }
      admit.
    }

    rewrite Hcrash_heaps_len.
    iModIntro.

    iIntros "#Hpos". iExists _, _. iFrame. iFrame "#".
    rewrite big_sepM_fmap /=. iFrame.
  }

  iIntros (npos ok) "Hnpos".
  wp_pures.
  wp_storeField.
  wp_loadField.
  destruct ok.
  {
    iDestruct "Hnpos" as "[Hnpos Htxn_pos]".
    iNamed "Hnpos".
    iDestruct "Htxn_pos" as (txn_num) "#Htxn_pos".
    wp_apply (release_spec with "[$Histxn_lock $Hlocked Hlockedheap Histxn_pos]").
    { iExists _, _, _. iFrame. }

    wp_pures.
    iApply "HΦ".
    iFrame.
    iExists txn_id. iFrame.
  }
  {
    iNamed "Hnpos".
    wp_apply (release_spec with "[$Histxn_lock $Hlocked Hlockedheap Histxn_pos]").
    { iExists _, _, _. iFrame. }

    wp_pures.
    iApply "HΦ". iFrame.
  }
Admitted.

Theorem wp_txn_CommitWait l q γ dinit bufs buflist bufamap (wait : bool) E (Q : nat -> iProp Σ) :
  {{{ is_txn l γ dinit ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      ( [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist, is_txn_buf_pre γ bufptrval a buf ) ∗
      ( |={⊤ ∖ ↑walN ∖ ↑invN, E}=> ∃ (σl : async (gmap addr {K & bufDataT K})),
          "Hcrashstates_frag" ∷ ghost_var γ.(txn_crashstates) (1/2) σl ∗
          "Hcrashstates_fupd" ∷ (
            let σ := ((λ b, existT _ b.(buf_).(bufData)) <$> bufamap) ∪ latest σl in
            ⌜bufamap ≠ ∅⌝ ∗
            ghost_var γ.(txn_crashstates) (1/2) (async_put σ σl)
            ={E, ⊤ ∖ ↑walN ∖ ↑invN}=∗ Q (length (possible σl))  ))
  }}}
    Txn__CommitWait #l (slice_val bufs) #wait
  {{{ (ok : bool), RET #ok;
      if ok then
        ( ⌜bufamap ≠ ∅⌝ -∗ ∃ (txn_id : nat),
          Q txn_id ∗
          ( ⌜wait=true⌝ -∗ own γ.(txn_walnames).(wal_heap_durable_lb) (◯ (MaxNat txn_id)) ) ) ∗
        [∗ map] a ↦ buf ∈ bufamap,
          mapsto_txn γ a (existT _ buf.(buf_).(bufData))
      else
        [∗ map] a ↦ buf ∈ bufamap,
          mapsto_txn γ a (existT buf.(buf_).(bufKind) buf.(data_))
  }}}.
Proof.
  iIntros (Φ) "(#Htxn & Hbufs & Hbufpre & Hfupd) HΦ".

  wp_call.
  wp_apply wp_ref_to; [val_ty|].
  iIntros (commit) "Hcommit".
  wp_pures.
  wp_apply wp_slice_len.
  wp_pures.
  rewrite bool_decide_decide.
  destruct (decide (int.val 0 < int.val bufs.(Slice.sz))).
  - wp_pures.

    iAssert (⌜ bufamap ≠ ∅ ⌝)%I as "%Hnotempty".
    {
      iIntros (H); subst.
      iDestruct (big_sepML_empty_l with "Hbufpre") as %->.
      iDestruct (is_slice_sz with "Hbufs") as "%Hlen".
      simpl in *; word.
    }

    wp_apply (wp_txn__doCommit with "[$Htxn $Hbufs $Hbufpre Hfupd]").
    {
      iMod "Hfupd".
      iModIntro.
      iNamed "Hfupd".
      iExists σl. iFrame "Hcrashstates_frag".

      iIntros "H".
      iMod ("Hcrashstates_fupd" with "[H]").
      { iFrame. done. }

      iModIntro. done.
    }

    iIntros (commitpos ok) "Hbufpost".

    wp_pures.
    destruct ok; wp_pures.
    + iDestruct "Hbufpost" as (txn_id) "(#Hpos & Hq & Hbufamap)".
      destruct wait; wp_pures.
      * iNamed "Htxn".
        wp_loadField.
        wp_apply (wp_Walog__Flush_heap with "[$Hiswal $Hpos]").
        iIntros "HQ".
        wp_load.
        iApply "HΦ". iFrame.
        iIntros (?). iExists txn_id. iFrame.
        done.

      * wp_pures.
        wp_load.
        iApply "HΦ". iFrame.
        iIntros (?). iExists txn_id. iFrame.
        iIntros (?). intuition congruence.

    + wp_apply util_proof.wp_DPrintf.
      wp_store.
      wp_load.
      iApply "HΦ".
      iFrame.

  - wp_apply util_proof.wp_DPrintf.

    iAssert (⌜ bufamap = ∅ ⌝)%I as "%Hempty".
    { destruct buflist.
      { iDestruct (big_sepML_empty_m with "Hbufpre") as %->. done. }
      iDestruct (is_slice_sz with "Hbufs") as "%Hlen". simpl in *.
      replace (int.val 0) with 0 in n by word. word.
    }

    wp_load.
    iApply "HΦ".

    iDestruct (is_slice_sz with "Hbufs") as %Hbuflistlen.
    assert (int.val bufs.(Slice.sz) = 0) by (revert n; word).
    assert (length (list.untype buflist) = 0%nat) by len.
    rewrite fmap_length in H0.
    apply length_zero_iff_nil in H0; subst.

    iSplit; last by iApply big_sepM_empty.
    iIntros. congruence.
Qed.


End goose_lang.
