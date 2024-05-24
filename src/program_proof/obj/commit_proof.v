From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.base_logic.lib Require Import mono_nat.

From Perennial.Helpers Require Import Transitions NamedProps Map.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.algebra Require Import auth_map log_heap.
From Perennial.base_logic Require Import lib.ghost_map.

From Goose.github_com.mit_pdos.go_journal Require Import obj.
From Goose.github_com.mit_pdos.go_journal Require Import wal.
From Perennial.program_proof Require Import wal.specs wal.lib wal.heapspec addr.addr_proof buf.buf_proof disk_lib.
From Perennial.program_proof Require Export obj.invariant obj.map_helpers.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section goose_lang.
Context `{!txnG Σ}.
Context `{!heapGS Σ}.

Implicit Types (s : Slice.t) (γ: txn_names).

Record buf_and_prev_data := {
  buf_ : buf;
  data_ : bufDataT buf_.(bufKind);
}.

Definition is_txn_buf_pre γ (bufptr:loc) (a : addr) (buf : buf_and_prev_data) : iProp Σ :=
  "Hisbuf" ∷ is_buf bufptr a buf.(buf_) ∗
  "Hmapto" ∷ pointsto_txn γ a (existT buf.(buf_).(bufKind) buf.(data_)).

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
    locked_wh_disk !! uint.Z blknum = Some diskLatest ->
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
  cut (uint.Z off = 0); [intros; word|].
  apply Z.div_exact in H0 as ->; [|word].
  rewrite Z.div_small; [|word].
  reflexivity.
Qed.

Theorem pointsto_txn_locked (γ : txn_names) l dinit lwh a data E :
  ↑invN ⊆ E ->
  ↑walN ⊆ E ∖ ↑invN ->
  is_wal (wal_heap_inv γ.(txn_walnames)) l (wal_heap_walnames γ.(txn_walnames)) dinit ∗
  ncinv invN (is_txn_always γ) ∗
  is_locked_walheap γ.(txn_walnames) lwh ∗
  pointsto_txn γ a data -∗
  |NC={E}=>
    is_locked_walheap γ.(txn_walnames) lwh ∗
    pointsto_txn γ a data ∗
    ⌜ ∃ v, locked_wh_disk lwh !! uint.Z a.(addrBlock) = Some v ⌝.
Proof.
  iIntros (H0 H1) "(#Hiswal & #Hinv & Hlockedheap & Hmapsto)".
  iInv "Hinv" as ">Htxnalways" "Hclo".
  iNamed "Htxnalways".
  iNamed "Hmapsto".
  iDestruct (map_valid with "Hmetactx Hmapsto_meta") as %Hvalid.
  eapply gmap_addr_by_block_lookup in Hvalid.
  destruct Hvalid as [offmap [Hmetam Hoffmap]].
  iDestruct (big_sepM2_lookup_r_some with "Hheapmatch") as (x) "%Hlm"; eauto.
  iDestruct (big_sepM2_lookup_acc with "Hheapmatch") as "[Hx Hheapmatch]"; eauto.
  iNamed "Hx".
  iMod (wal_heap_pointsto_latest with "[$Hiswal $Hlockedheap $Htxn_hb]") as "(Hlockedheap & Htxn_hb & %)"; eauto.
  iMod ("Hclo" with "[-Hlockedheap Hmapsto_log Hmapsto_meta Hmod_frag]").
  { iNext. iExists _, _, _. iFrame.
    iApply "Hheapmatch". iExists _, _, _. iFrame. iFrame "%". }
  iModIntro.
  iFrame. eauto.
Qed.

Theorem wp_txn__installBufsMap l q walptr γ dinit lwh bufs buflist (bufamap : gmap addr buf_and_prev_data) :
  {{{ ncinv invN (is_txn_always γ) ∗
      is_wal (wal_heap_inv γ.(txn_walnames)) walptr (wal_heap_walnames γ.(txn_walnames)) dinit ∗
      readonly (l ↦[obj.Log :: "log"] #walptr) ∗
      is_locked_walheap γ.(txn_walnames) lwh ∗
      own_slice bufs ptrT q buflist ∗
      [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist,
        is_txn_buf_pre γ bufptrval a buf
  }}}
    Log__installBufsMap #l (slice_val bufs)
  {{{ (blkmapref : loc) (blkmap : gmap u64 Slice.t), RET #blkmapref;
      is_locked_walheap γ.(txn_walnames) lwh ∗
      own_map blkmapref (DfracOwn 1) blkmap ∗
      ( [∗ map] a ↦ buf ∈ bufamap,
        pointsto_txn γ a (existT buf.(buf_).(bufKind) buf.(data_)) ) ∗
      [∗ map] blkno ↦ blkslice; offmap ∈ blkmap; gmap_addr_by_block bufamap,
        ∃ b,
          is_block blkslice (DfracOwn 1) b ∗
          ⌜ updBlockKindOK blkno b γ (locked_wh_disk lwh) (buf_ <$> offmap) ⌝
  }}}.
Proof using txnG0 txnG0 Σ.
  iIntros (Φ) "(#Hinv & #Hiswal & #log & Hlockedheap & Hbufs & Hbufpre) HΦ".

Opaque struct.t.
  wp_call.
  wp_apply wp_NewMap.
  iIntros (blks) "Hblks".

  iDestruct (own_slice_to_small with "Hbufs") as "Hbufs".
  wp_apply (wp_forSlicePrefix
      (fun done todo =>
        ∃ bufamap_todo bufamap_done blkmap,
        "<-" ∷ ⌜ done ++ todo = buflist ⌝ ∗
        "->" ∷ ⌜ bufamap_done = bufamap ∖ bufamap_todo ⌝ ∗
        "%" ∷ ⌜ bufamap_todo ⊆ bufamap ⌝ ∗
        "Hblks" ∷ own_map blks (DfracOwn 1) blkmap ∗
        "Hbufamap_todo" ∷ ( [∗ maplist] a↦buf;bufptrval ∈ bufamap_todo;todo, is_txn_buf_pre γ bufptrval a buf ) ∗
        "Hbufamap_done" ∷ ( [∗ map] blkno ↦ blkslice; offmap ∈ blkmap; gmap_addr_by_block bufamap_done,
          ∃ b,
            is_block blkslice (DfracOwn 1) b ∗
            ⌜ updBlockKindOK blkno b γ (locked_wh_disk lwh) (buf_ <$> offmap) ⌝ ) ∗
        "Hbufamap_done_pointsto" ∷ ( [∗ map] a↦buf ∈ bufamap_done, pointsto_txn γ a (existT buf.(buf_).(bufKind) buf.(data_)) ) ∗
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

    iMod (pointsto_txn_locked with "[$Hiswal $Hinv $Hmapto $Hlockedheap]") as "(Hlockedheap & Hmapto & %Hlockedsome)".
    1: solve_ndisj.
    1: solve_ndisj.
    destruct Hlockedsome as [lockedv Hlockedsome].

    wp_pures.
    wp_apply (wp_buf_loadField_sz with "Hisbuf"). iIntros "Hisbuf".
    destruct (decide (buf.(buf_).(bufKind) = KindBlock)).

    - replace (bufSz buf.(buf_).(bufKind)) with (bufSz KindBlock) by congruence.
      Opaque BlockSize. Opaque bufSz.
      wp_pures.

      iMod (pointsto_txn_valid with "Hinv Hmapto") as "[Hmapto %Hvalid]".
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
      { iPureIntro. erewrite difference_delete; eauto.
        eapply lookup_weaken; eauto. }
      iFrame "Hblks".
      iFrame "Hbufamap_todo".

      iFrame "Hlockedheap".
      iSplitR.
      { iPureIntro. etransitivity; first by apply delete_subseteq. eauto. }
      iSplitR "Hbufamap_done_pointsto Hmapto".
      2: {
        iApply (big_sepM_insert_2 with "[Hmapto] Hbufamap_done_pointsto").
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
        { inversion Heqb0. }
        { inversion Heqb0. }
      }

      wp_apply wp_ref_of_zero; first by eauto.
      iIntros (blkvar) "Hblkvar".

      wp_apply (wp_buf_loadField_addr with "Hisbuf"). iIntros "Hisbuf".
      wp_apply (wp_MapGet with "Hblks"). iIntros (v ok) "[% Hblks]".
      wp_pures.

      iMod (pointsto_txn_valid with "Hinv Hmapto") as "[Hmapto %Hvalid]".
      { solve_ndisj. }

      wp_apply (wp_If_join
        ( ∃ blkslice blk blkmap',
            "Hblkvar" ∷ blkvar ↦[slice.T byteT] (slice_val blkslice) ∗
            "Hisblock" ∷ is_block blkslice (DfracOwn 1) blk ∗
            "Hbufamap_done" ∷ ( [∗ map] blkno↦blkslice;offmap ∈ delete a.(addrBlock) blkmap';
                  delete a.(addrBlock) (gmap_addr_by_block (bufamap ∖ bufamap_todo)),
                  ∃ b0 : Block,
                    is_block blkslice (DfracOwn 1) b0
                    ∗ ⌜updBlockKindOK blkno b0 γ
                         (locked_wh_disk lwh) (buf_ <$> offmap)⌝ ) ∗
            "Hisbuf" ∷ is_buf b a buf.(buf_) ∗
            "Hlockedheap" ∷ is_locked_walheap γ.(txn_walnames) lwh ∗
            "Hblks" ∷ own_map blks (DfracOwn 1) blkmap' ∗
            "%" ∷ ⌜ blkmap' !! a.(addrBlock) = Some blkslice ⌝ ∗
            "%" ∷ ⌜ updBlockOK a.(addrBlock) blk buf.(buf_).(bufKind) (locked_wh_disk lwh) (default ∅ ((gmap_addr_by_block (buf_ <$> (bufamap ∖ bufamap_todo))) !! a.(addrBlock))) ⌝
        )%I
        with "[Hbufamap_done Hisbuf Hblkvar Hlockedheap Hblks]"); first iSplit.
      {
        iIntros "->".
        wp_store.
        apply map_get_true in H0.
        iDestruct (big_sepM2_lookup_l_some with "Hbufamap_done") as (xx) "%Hx"; eauto.
        iDestruct (big_sepM2_delete with "Hbufamap_done") as "[Ha Hbufamap_done]"; eauto.
        iDestruct "Ha" as (b0) "[Hisblock %]".
        iSplitR; first done.
        iExists _, _, _. iFrame. iModIntro.
        iSplit; first by done.
        iPureIntro.
        rewrite gmap_addr_by_block_fmap.
        rewrite lookup_fmap.
        rewrite Hx. simpl.
        destruct H1. destruct H1. intuition idtac.
        rewrite H1 in H6. inversion H6; clear H6; subst. eauto.
      }
      {
        iIntros "->".
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
        iSplitR; first done.
        iExists _, _, _. iFrame.

        apply map_get_false in H0; destruct H0; subst.
        iDestruct (big_sepM2_lookup_l_none with "Hbufamap_done") as %Hnone; eauto.

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
      { iPureIntro. erewrite difference_delete; eauto.
        erewrite lookup_weaken; eauto. }
      iSplitR.
      { iPureIntro. etransitivity; first by apply delete_subseteq. eauto. }
      iSplitR "Hbufamap_done_pointsto Hmapto".
      2: {
        iApply (big_sepM_insert_2 with "[Hmapto] [$Hbufamap_done_pointsto]").
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
  iApply "HΦ". by iFrame.
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
  {{{ ncinv invN (is_txn_always γ) ∗
      is_wal (wal_heap_inv γ.(txn_walnames)) walptr (wal_heap_walnames γ.(txn_walnames)) dinit ∗
      readonly (l ↦[obj.Log :: "log"] #walptr) ∗
      is_locked_walheap γ.(txn_walnames) lwh ∗
      own_slice bufs ptrT q buflist ∗
      [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist,
        is_txn_buf_pre γ bufptrval a buf
  }}}
    Log__installBufs #l (slice_val bufs)
  {{{ (blkslice : Slice.t) upds, RET (slice_val blkslice);
      is_locked_walheap γ.(txn_walnames) lwh ∗
      updates_slice blkslice upds ∗
      ( [∗ map] a ↦ buf ∈ bufamap,
        pointsto_txn γ a (existT buf.(buf_).(bufKind) buf.(data_)) ) ∗
      [∗ maplist] blkno ↦ offmap; upd ∈ gmap_addr_by_block bufamap; upds,
        ⌜ upd.(update.addr) = blkno ⌝ ∗
        ⌜ updBlockKindOK blkno upd.(update.b) γ (locked_wh_disk lwh) (buf_ <$> offmap) ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hinv & #Hiswal & #Hlog & Hlockedheap & Hbufs & Hbufpre) HΦ".

  wp_call.
  wp_apply (wp_txn__installBufsMap with "[$Hinv $Hiswal $Hlog $Hlockedheap $Hbufs $Hbufpre]").
  iIntros (blkmapref blkmap) "(Hlockedheap & Hblkmapref & Hbufamap_pointsto & Hblkmap)".

  wp_apply (wp_MapLen with "Hblkmapref").
  (* we don't use this length, it's just a slice capacity *)
  iIntros "[%_ Hblkmapref]".
  wp_apply wp_NewSliceWithCap.
  { word. }
  iIntros (ptr) "Hblks_slice".
  rewrite replicate_0.
  set (blks_s := Slice.mk ptr 0 _).
  wp_apply wp_ref_to; first by eauto.
  iIntros (blks_var) "Hblks_var".

  wp_apply (wp_MapIter_2 _ _ _ _ _
    (λ mtodo mdone,
      ∃ (blks : Slice.t) upds offmaps_todo offmaps_done,
        "Hblks_var" ∷ blks_var ↦[slice.T (struct.t Update)] (slice_val blks) ∗
        "Hblks" ∷ updates_slice blks upds ∗
        "%" ∷ ⌜ gmap_addr_by_block bufamap = offmaps_todo ∪ offmaps_done ⌝ ∗
        "%" ∷ ⌜ dom offmaps_todo ## dom offmaps_done ⌝ ∗
        "Hmtodo" ∷ ( [∗ map] blkno↦blkslice;offmap ∈ mtodo;offmaps_todo, ∃ b : Block,
                                          is_block blkslice (DfracOwn 1) b ∗
                                          ⌜ updBlockKindOK blkno b γ (locked_wh_disk lwh) (buf_ <$> offmap) ⌝ ) ∗
        "Hmdone" ∷ ( [∗ maplist] blkno↦offmap;upd ∈ offmaps_done;upds,
                                          ⌜ upd.(update.addr) = blkno ⌝ ∗
                                          ⌜ updBlockKindOK blkno upd.(update.b) γ (locked_wh_disk lwh) (buf_ <$> offmap) ⌝ )
    )%I with "Hblkmapref [Hblks_var Hblkmap Hblks_slice]").
  {
    iExists _, nil, _, ∅.
    iFrame "Hblks_var".
    iFrame "Hblkmap".
    iSplitL.
    { rewrite /updates_slice. iExists nil. simpl.
      iSplitL; last by done.
      iFrame.
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

    iDestruct (big_sepM2_lookup_l_some with "Hmtodo") as (x) "%Hx"; eauto.
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
    { iPureIntro. rewrite H0. rewrite union_delete_insert; eauto. }
    iSplitR.
    { iPureIntro. set_solver. }
    iApply big_sepML_insert_app.
    { eapply (not_elem_of_dom (D:=gset u64)).
      assert (k ∈ dom offmaps_todo).
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
  by iFrame.
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

Lemma latest_update_app c : ∀ b a,
  latest_update a (b ++ [c]) = c.
Proof.
  induction b; simpl; eauto.
Qed.

Lemma big_sepL2_async_latest {X Y} (xx : async X) (yy : async Y) (P : nat -> X -> Y -> iProp Σ) :
  ( [∗ list] k↦x;y ∈ possible xx;possible yy, P k x y ) -∗
  P (length xx.(pending)) xx.(latest) yy.(latest).
Proof.
  iIntros "H".
  iDestruct (big_sepL2_snoc with "H") as "[H Hlatest]".
  iApply "Hlatest".
Qed.

Lemma apply_upds_u64_dom : ∀ upds d,
  ( ∀ blkno,
    blkno ∈ update.addr <$> upds ->
    blkno ∈ dom d ) ->
  dom (apply_upds_u64 d upds) =
  dom d.
Proof.
  induction upds; simpl; eauto; intros.
  rewrite IHupds.
  - rewrite dom_insert_L.
    assert (a.(update.addr) ∈ dom d); last by set_solver.
    eapply H. constructor.
  - intros.
    destruct (decide (blkno = a.(update.addr))); subst.
    + apply elem_of_dom. rewrite lookup_insert. eauto.
    + apply elem_of_dom. rewrite lookup_insert_ne; eauto. rewrite -elem_of_dom.
      eapply H. econstructor. eauto.
Qed.

Lemma apply_upds_u64_lookup_ne blkno : ∀ upds d,
  blkno ∉ update.addr <$> upds ->
  apply_upds_u64 d upds !! blkno = d !! blkno.
Proof.
  induction upds; simpl; eauto; intros.
  eapply not_elem_of_cons in H; destruct H as [H H'].
  rewrite IHupds; eauto.
  rewrite lookup_insert_ne; eauto.
Qed.

Lemma apply_upds_u64_lookup lv : ∀ updlist_olds d,
  lv ∈ updlist_olds ->
  NoDup ((λ lv : update.t * (Block * list Block), (lv.1).(update.addr)) <$> updlist_olds) ->
  apply_upds_u64 d updlist_olds.*1 !! (lv.1).(update.addr) = Some (lv.1).(update.b).
Proof.
  induction updlist_olds; simpl; intros.
  { inversion H. }
  inversion H0; clear H0; subst.
  rewrite apply_upds_u64_insert.
  2: {
    rewrite -list_fmap_map.
    rewrite -list_fmap_compose.
    eapply H3.
  }
  inversion H; clear H; subst.
  { rewrite lookup_insert. eauto. }
  rewrite lookup_insert_ne.
  { apply IHupdlist_olds; eauto. }
  intro H. rewrite H in H3. apply H3.
  eapply elem_of_list_fmap_1_alt; eauto.
Qed.

Definition txn_crashstates_matches_pointsto σl γ σl' a v :
  ( ( ghost_map_auth γ.(txn_logheap) 1 (latest σl) ∗ ghost_var γ.(txn_crashstates) (1/4) σl ) ∗
    ghost_var γ.(txn_crashstates) (3/4) σl' ∗
    pointsto_txn γ a v ) -∗
  ⌜σl'.(latest) !! a = Some v⌝.
Proof.
  iIntros "[[Hctx H0] [H1 Hmapsto]]".
  iNamed "Hmapsto".
  iDestruct (ghost_map_lookup with "Hctx Hmapsto_log") as %Heq.
  iDestruct (ghost_var_agree with "H0 H1") as %->.
  done.
Qed.

Theorem wp_txn__doCommit l q γ dinit bufs buflist (bufamap : gmap addr _) E (PreQ: iProp Σ) (Q : nat -> iProp Σ) :
  {{{ is_txn l γ dinit ∗
      own_slice bufs ptrT q buflist ∗
      ( [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist, is_txn_buf_pre γ bufptrval a buf ) ∗
      PreQ ∧ (|NC={⊤ ∖ ↑walN ∖ ↑invN, E}=>
        ∀ CP,
        □ ( ∀ σl a v,
          ( CP ∗ ghost_var γ.(txn_crashstates) (3/4) σl ∗ pointsto_txn γ a v ) -∗ ⌜σl.(latest) !! a = Some v⌝ ) ∗
        CP
        -∗ |NC={E}=>
        CP ∗
        ∃ (σl : async (gmap addr {K & bufDataT K})),
          "Hcrashstates_frag" ∷ ghost_var γ.(txn_crashstates) (3/4) σl ∗
          "Hcrashstates_fupd" ∷ (
            let σ : gmap addr {K & bufDataT K} :=
               ((λ b, existT b.(buf_).(bufKind) b.(buf_).(bufData)) <$> bufamap) ∪ latest σl in
            ghost_var γ.(txn_crashstates) (3/4) (async_put σ σl)
           -∗ |NC={E, ⊤ ∖ ↑walN ∖ ↑invN}=> Q (length (possible σl)) ))
  }}}
    Log__doCommit #l (slice_val bufs)
  {{{ (commitpos : u64) (ok : bool), RET (#commitpos, #ok);
      if ok then
        ∃ txn_id,
        txn_pos (wal_heap_walnames (txn_walnames γ)) txn_id commitpos ∗ Q txn_id ∗
        [∗ map] a ↦ buf ∈ bufamap,
          pointsto_txn γ a (existT _ buf.(buf_).(bufData))
      else
        PreQ ∗
        ([∗ map] a ↦ buf ∈ bufamap,
          pointsto_txn γ a (existT buf.(buf_).(bufKind) buf.(data_)))
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
     "Hmapstos" ∷ ([∗ map] a↦buf ∈ bufamap, pointsto_txn γ a (existT _ buf.(data_))) ∗
     "HPreQ" ∷ PreQ)
    (λ npos,
      ∃ lwh' txn_id,
        "Hlockedheap" ∷ is_locked_walheap γ.(txn_walnames) lwh' ∗
        "Hmapstos" ∷ ( [∗ map] k↦x ∈ bufamap, pointsto_txn γ k (existT _ x.(buf_).(bufData)) ) ∗
        "Hpos" ∷ txn_pos (wal_heap_walnames (txn_walnames γ)) txn_id npos ∗
        "HQ" ∷ Q txn_id
    )%I
    with "[$Hiswal $Hblks Hmapstos Hwal_latest Hfupd]").
  { iApply (wal_heap_memappend E with "[Hfupd] Hwal_latest Hmapstos").
    iSplit; [ iDestruct "Hfupd" as "[$ _]" | iRight in "Hfupd" ].
    iInv invN as ">Hinner" "Hinner_close".
    iIntros (σ) "(Hmapstos & Hwal_latest & Hiswal_heap)".
    iMod "Hfupd".
    iNamed "Hinner".

    iMod ("Hfupd" with "[Hlogheapctx Hcrashstates]") as "Hfupd".
    {
      iSplitR.
      { iModIntro. iIntros (σl a v) "(CP & H & Hmapsto)".
        iApply (txn_crashstates_matches_pointsto logm). iFrame "H Hmapsto".
        iExact "CP". }
      iFrame.
    }

    iModIntro.
    iDestruct "Hfupd" as "[[Hlogheapctx Hcrashstates] Hfupd]".
    iNamed "Hfupd".

    rewrite /memappend_pre.
    rewrite /memappend_crash_pre.

    iDestruct (ghost_var_agree with "Hcrashstates Hcrashstates_frag") as %->.

    iAssert (⌜ ∀ a, a ∈ dom bufamap -> a ∈ dom σl.(latest) ⌝)%I as "%Hsubset_addr".
    {
      iIntros (a Ha).
      eapply elem_of_dom in Ha. destruct Ha.
      iDestruct (big_sepM_lookup with "Hmapstos") as "Ha"; eauto.
      iNamed "Ha".
      iDestruct (ghost_map_lookup with "Hlogheapctx Hmapsto_log") as %Hvalid.
      iPureIntro.
      apply elem_of_dom. rewrite Hvalid. eauto.
    }
    apply elem_of_subseteq in Hsubset_addr.

    iDestruct (gmap_addr_by_block_big_sepM with "Hmapstos") as "Hmapstos".

    iAssert (⌜ ∀ a, a ∈ dom (gmap_addr_by_block bufamap) -> a ∈ dom (gmap_addr_by_block σl.(latest)) ⌝)%I as "%Hsubset".
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
      iDestruct (ghost_map_lookup with "Hlogheapctx Hmapsto_log") as %Hvalid.
      eapply gmap_addr_by_block_lookup in Hvalid as Hvalidblock; destruct Hvalidblock; intuition idtac.
      iPureIntro.
      apply elem_of_dom. rewrite H0. eauto.
    }
    apply elem_of_subseteq in Hsubset.

    iDestruct (big_sepML_sep with "Hupdmap") as "[Hupdmap_addr Hupdmap_kind]".

    iDestruct (big_sepML_change_m _
      (filter (λ (k : u64 * _), fst k ∈ dom (gmap_addr_by_block bufamap)) (gmap_addr_by_block σl.(latest)))
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
          lv.(update.addr) ↪[_] (HB (fst installed_bs) (snd installed_bs))
      )%I with "Hheapmatch []") as "Hheapmatch".
    {
      iIntros (k v lv). iPureIntro.
      iIntros "(<- & H)".
      iDestruct "H" as (v0) "(% & H)".
      iDestruct "H" as (installed bs blockK) "(% & H0 & H1)".
      iExists (installed, bs). iFrame. done. }

    iDestruct (big_sepML_exists with "Hheapmatch") as (updlist_olds) "[-> Hheapmatch]".
    iExists (snd <$> updlist_olds).
    iExists crash_heaps.

    iDestruct (lwh_crash_heaps with "Hcrashheaps Hwal_latest Hiswal_heap") as (lwh_installed lwh_durable) "#Hlwh_crash_heaps".

    iAssert (⌜∀ lv, lv ∈ updlist_olds ->
             apply_upds (txn_upds lwh.(locked_wh_σtxns)) lwh.(locked_wh_σd) !! uint.Z (lv.1).(update.addr) = Some (latest_update lv.2.1 lv.2.2)⌝)%I
      as "%Hlwh_any".
    {
      iIntros (lv Hlv).
      eapply elem_of_list_lookup_1 in Hlv. destruct Hlv as [i Hlv].
      iDestruct (big_sepML_lookup_l_acc with "Hheapmatch") as (k v) "(% & Hlv & _)"; eauto.
      iDestruct "Hlv" as "[_ Hlv]".
      iDestruct (wal_heap_pointsto_latest_helper with "[$Hiswal_heap $Hwal_latest $Hlv]") as "%Hlwh_ok".
      eauto.
    }
    iAssert (⌜∀ lv, lv ∈ updlist_olds ->
                update.addr (fst lv) ∈ dom (gmap_addr_by_block bufamap)⌝)%I
      as "%Hupdlist_olds_σl_latest".
    {
      iIntros (lv Hlv).
      eapply elem_of_list_lookup_1 in Hlv. destruct Hlv as [i Hlv].
      iDestruct (big_sepML_lookup_l_acc with "Hheapmatch") as (k v) "(% & Hlv & _)"; eauto.
      iDestruct "Hlv" as "[Hlv _]".
      iDestruct "Hlv" as (blockK v0) "(<- & _ & _ & _)".
      eapply map_lookup_filter_Some_1_2 in H as H'.
      eauto.
    }
    iAssert (⌜∀ (blkno : u64),
              blkno ∈ dom (gmap_addr_by_block bufamap) ->
              blkno ∈ update.addr <$> updlist_olds.*1⌝)%I
      as "%Hupdlist_olds_bufamap".
    {
      iIntros (blkno Hblkno).
      apply elem_of_dom in Hblkno; destruct Hblkno.
      iDestruct (big_sepML_lookup_m_acc with "Hupdmap_addr") as (i lv) "(% & <- & _)"; eauto.
      iPureIntro.
      eapply elem_of_list_lookup_2.
      rewrite list_lookup_fmap. erewrite H0. done.
    }
    iModIntro.
    iFrame "Hwal_latest".
    iFrame "Hcrashheaps".
    iFrame "Hiswal_heap".

    iDestruct (big_sepML_sepL_split with "Hheapmatch") as "[Hheapmatch Hupdlist_olds]".

    iSplitL "Hupdlist_olds".
    {
      iApply big_sepL2_alt.
      iSplitR.
      { repeat rewrite fmap_length. eauto. }
      rewrite zip_fst_snd. iFrame.
    }

    iIntros (pos') "(Hcrash & Hq)".
    rewrite /memappend_crash /memappend_q.

    iDestruct "Hcrash" as "(Hlockedheap & Hcrashheaps)".
    rewrite (big_sepL2_alt _ updlist_olds.*1).
    iDestruct "Hq" as "[_ Hq]".
    rewrite zip_fst_snd.

    remember (((λ b, existT _ b.(buf_).(bufData)) <$> bufamap) ∪ σl.(latest)) as σl'latest.

    pose proof (filter_union_gmap_addr_by_block_ignored σl.(latest)
                  ((λ b, existT _ b.(buf_).(bufData)) <$> bufamap)
                  (λ x, x ∉ dom (gmap_addr_by_block bufamap))) as Hy.
    rewrite Hy.
    2: {
      intros k a Hka.
      rewrite lookup_fmap in Hka. apply fmap_Some_1 in Hka. destruct Hka. intuition. apply H0; clear H0.
      eapply gmap_addr_by_block_lookup in H1. destruct H1. intuition.
      apply elem_of_dom. eauto.
    }

    iDestruct (gmap_addr_by_block_big_sepM' _
      (λ a v, pointsto_txn γ a (existT v.(buf_).(bufKind) v.(data_)))
      with "Hmapstos") as "Hmapstos".

    iDestruct (big_sepML_sepL_combine with "[$Hheapmatch $Hq]") as "Hheapmatch".
    iDestruct (big_sepML_nodup (λ lv, lv.1.(update.addr)) with "Hheapmatch []") as "%Hnodup".
    { iIntros (k1 k2 v1 v2 lv1 lv2 H) "[H0 _] [H1 _]".
      iDestruct "H0" as (??) "[% _]".
      iDestruct "H1" as (??) "[% _]". iPureIntro. congruence. }

    iDestruct (big_sepML_sepM_ex with "Hheapmatch") as "Hheapmatch".
    iDestruct (big_sepM_mono_dom_Q with "[] [Hmapstos Hmetactx Hheapmatch]") as "[Hmapstos_and_metactx Hheapmatch]".
    4: iDestruct (big_sepM_filter_split with "[$Hheapmatch $Hheapmatch_rebuild]") as "Hheapmatch".
    3: {
      iSplitL "Hmapstos Hmetactx". { iAccu. }
      iExact "Hheapmatch".
    }
    { simpl. epose proof (dom_filter_eq (gmap_addr_by_block σl.(latest)) _ (λ x, x ∈ dom (gmap_addr_by_block bufamap))) as He.
      rewrite He. 1: reflexivity.
      rewrite gmap_addr_by_block_dom_union.
      rewrite gmap_addr_by_block_fmap. rewrite dom_fmap_L. set_solver. }
    { simpl. iModIntro. iIntros (k offmap Hoffmap) "[[Hmapstos Hmetactx] H]".
      iDestruct "H" as (lv) "(%Hlv_in & H & Hmapsto)".

      iAssert (⌜apply_upds (txn_upds lwh.(locked_wh_σtxns)) lwh.(locked_wh_σd) !! uint.Z (lv.1).(update.addr) = Some (latest_update lv.2.1 lv.2.2)⌝)%I as "%Hlwh".
      { eauto. }

      iDestruct "H" as (blockK meta) "(% & % & % & Hinblock)".
      eapply map_lookup_filter_Some_1_2 in Hoffmap as Hbufamap_in.
      eapply elem_of_dom in Hbufamap_in. destruct Hbufamap_in as [offmap' Hbufamap_in].
      iExists (((λ b, existT b.(buf_).(bufKind) b.(buf_).(bufData)) <$> offmap') ∪ offmap).
      iSplit.
      { iPureIntro. eapply map_lookup_filter_Some_2.
        2: { simpl. eapply elem_of_dom. eauto. }
        eapply map_lookup_filter_Some_1_1 in Hoffmap.
        eapply gmap_addr_by_block_union_lookup; eauto.
        rewrite gmap_addr_by_block_fmap lookup_fmap Hbufamap_in //.
      }
      subst.

      assert (dom offmap' ⊆ dom offmap).
      {
        eapply map_lookup_filter_Some_1_1 in Hoffmap.
        eapply elem_of_subseteq; intros off Hoff'.
        eapply elem_of_dom in Hoff'. destruct Hoff' as [x Hoff'].
        replace (offmap' !! off) with (bufamap !! ((lv.1).(update.addr), off)) in Hoff'.
        2: {
          rewrite -lookup_gmap_curry. rewrite Hbufamap_in. done.
        }
        assert (((lv.1).(update.addr), off) ∈ dom σl.(latest)).
        { eapply elem_of_dom_2 in Hoff'. set_solver. }
        eapply elem_of_dom in H. destruct H as [x' H].
        rewrite -lookup_gmap_curry in H. rewrite Hoffmap /= in H.
        eapply elem_of_dom; eauto.
      }

      iDestruct (big_sepML_lookup_m_acc with "Hupdmap") as (i u) "(% & % & _)"; eauto.
      intuition idtac.
      destruct H5 as [bk [Hbk Hcontents]].
      rewrite Hbk in H1. inversion H1; clear H1; subst.
      eapply Hcontents in Hlwh.

      assert (u = lv.1); subst.
      {
        eapply elem_of_list_lookup_1 in Hlv_in. destruct Hlv_in as [j Hlv_in].
        rewrite list_lookup_fmap in H2.
        destruct (updlist_olds !! i) eqn:Hu'; simpl in *; try congruence.
        destruct (decide (i = j)); subst; try congruence.
        exfalso. apply n. eapply NoDup_lookup; eauto.
        { rewrite list_lookup_fmap. rewrite Hu'. eauto. }
        { rewrite list_lookup_fmap. rewrite Hlv_in /=. rewrite -H4. congruence. }
      }

      rewrite /bufDataTs_in_block.
      iDestruct (big_sepM2_dom with "Hinblock") as "%Hdomeq".
      iDestruct (big_sepM2_sepM_1 with "Hinblock") as "Hinblock".
      iDestruct (big_sepM_mono_dom_Q _ _
        (λ k y1,
          ∃ y2 : gname,
            ⌜meta !! k = Some y2⌝
            ∗ (∃ modifiedSinceInstall : bool,
                 "%Hoff_in_block" ∷ ⌜bufDataT_in_block (latest_update lv.2.1 lv.2.2) blockK (lv.1).(update.addr) k y1⌝ ∗
                 "Hoff_own" ∷ ghost_var y2 (1 / 2) modifiedSinceInstall ∗
                 "%Hmod_bufamap" ∷ ⌜k ∈ dom offmap' -> modifiedSinceInstall = true⌝ ∗
                 "%Hoff_prefix_in_block" ∷ ⌜if modifiedSinceInstall
                        then True
                        else
                         ∀ prefix : nat,
                           bufDataT_in_block
                             (latest_update lv.2.1 (take prefix lv.2.2)) blockK
                             (lv.1).(update.addr) k y1⌝))%I
        offmap offmap with "[] [Hmapstos Hmetactx Hinblock]") as "[Hmapstos_and_metactx Hinblock]".
      { eauto. }
      2: iSplitL "Hmapstos Hmetactx"; [ iAccu | iExact "Hinblock" ].
      { iIntros (k x Hkx). iModIntro. iIntros "[[Hmapstos Hmetactx] H]".
        iExists x. iSplit; first done.
        iDestruct "H" as (γmeta) "[% H]".
        iDestruct "H" as (modsince) "(% & Hmod & %)".
        destruct (decide (k ∈ dom offmap')).
        {
          apply elem_of_dom in e. destruct e.
          iDestruct (big_sepM_lookup_acc _ bufamap ((lv.1).(update.addr), k) with "Hmapstos") as "[Hk Hmapstos]".
          { erewrite <- (lookup_gmap_curry bufamap). rewrite Hbufamap_in /=. eauto. }
          iNamed "Hk".
          iDestruct (map_valid with "Hmetactx Hmapsto_meta") as "%Hmeta_name".
          rewrite <- (lookup_gmap_curry metam) in Hmeta_name. rewrite H0 /= in Hmeta_name.
          replace (γmeta) with (γm) by congruence.
          iDestruct (ghost_var_agree with "Hmod Hmod_frag") as %->.
          iDestruct ("Hmapstos" with "[Hmapsto_log Hmapsto_meta Hmod_frag]") as "Hmapstos".
          { iExists _. iFrame. }
          iFrame "∗%". iPureIntro; eauto.
        }
        iFrame "∗%". iPureIntro; eauto.
      }
      iDestruct "Hmapstos_and_metactx" as "[Hmapstos Hmetactx]".
      iFrame.

      iExists _. iSplit; eauto.
      iExists _. iSplit; eauto.

      iApply big_sepM_sepM2_merge_ex.
      { rewrite -Hdomeq. rewrite dom_union_L. rewrite dom_fmap_L. set_solver. }

      iApply (big_sepM_mono_dom with "[] Hinblock").
      { rewrite dom_union_L. rewrite dom_fmap_L. set_solver. }

      iIntros (k x Hkx). iModIntro. iIntros "H".
      iDestruct "H" as (γmeta) "(% & H)".
      iDestruct "H" as (modsince) "(%Hoff & Hmeta & %Hin_true & %Hmod)".
      specialize (Hlwh k).

      destruct (offmap' !! k) eqn:Hoff'k.
      {
        rewrite Hin_true. 2: { eapply elem_of_dom; eauto. }
        iExists _. iSplit.
        { iPureIntro. apply lookup_union_Some_l. rewrite lookup_fmap Hoff'k. done. }
        iExists γmeta. iSplit; first done.
        iExists _; iFrame.
        iPureIntro.
        rewrite /bufDataT_in_block /= in Hoff. intuition subst.
        eapply Hlwh in H3; eauto.
        rewrite lookup_fmap Hoff'k /= in H3. destruct H3. rewrite -H7 in H5.
        rewrite /bufDataT_in_block /=. intuition eauto.
        rewrite latest_update_app; eauto.
      }

      iExists x.
      iSplit.
      { iPureIntro. rewrite lookup_union_r; eauto. rewrite lookup_fmap Hoff'k //. }
      iExists _; iSplit; first done.
      iExists _; iFrame.
      iSplit.
      {
        iPureIntro. revert Hoff. rewrite /bufDataT_in_block. intuition eauto; subst.
        eapply Hlwh in H3; eauto.
        rewrite lookup_fmap Hoff'k /= in H3.
        rewrite latest_update_app; eauto.
      }
      {
        destruct modsince; eauto.
        iPureIntro. intros prefix.
        destruct (decide (length (lv.2.2 ++ [(lv.1).(update.b)]) ≤ prefix)).
        { rewrite take_ge; last by lia.
          revert Hoff. rewrite /bufDataT_in_block. intuition eauto; subst.
          eapply Hlwh in H3; eauto.
          rewrite lookup_fmap Hoff'k /= in H3.
          rewrite latest_update_app; eauto. }
        rewrite take_app_le. 2: { rewrite app_length /= in n. lia. }
        eauto.
      }
    }

    iDestruct "Hmapstos_and_metactx" as "[Hmapstos Hmetactx]".

    iDestruct "Hcrashheapsmatch" as "#Hcrashheapsmatch".
    iDestruct (big_sepL2_length with "Hcrashheapsmatch") as "%Hcrash_heaps_len".
    iMod (ghost_var_update_parts (async_put σl'latest σl) with "Hcrashstates Hcrashstates_frag") as "[Hcrashstates Hcrashstates_frag]".
    { rewrite Qp.quarter_three_quarter //. }

    iDestruct (pointsto_txn_cur_map _ _ _
      (λ b, Build_buf_and_prev_data (b.(buf_)) (b.(buf_).(bufData)))
      with "Hmapstos") as "[Hmapsto_cur Hmapstos]".
    set σmod := ((λ b : buf_and_prev_data, existT b.(buf_).(bufKind) b.(buf_).(bufData)) <$> bufamap).
    iMod (ghost_map_update_big_exist σmod with "Hlogheapctx [Hmapsto_cur]") as "[Hlogheapctx Hnewmapsto]".
    { iApply (big_sepM_mono_dom with "[] Hmapsto_cur").
      { rewrite dom_fmap_L. done. }
      iModIntro. iIntros (k x Hkx) "Hmapsto_cur".
      iExists _. rewrite lookup_fmap Hkx /=. iSplit; first by done.
      iExists _. iFrame. }
    change (σmod ∪ σl.(latest)) with (latest $ async_put (σmod ∪ σl.(latest)) σl).
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

      iFrame "Hcrashheapsmatch".
      iSplit; last done.
      simpl.
      iDestruct (big_sepL2_async_latest with "Hcrashheapsmatch") as "Hcrashheap_latest".
      iApply big_sepM2_forall.
      iSplit.
      { iDestruct (big_sepM2_dom with "Hcrashheap_latest") as "%Hlatestdom".
        iPureIntro. intros.
        rewrite -?elem_of_dom gmap_addr_by_block_dom_union.
        rewrite gmap_addr_by_block_fmap dom_fmap.
        rewrite subseteq_union_1_L; eauto.

        assert (∀ (blkno : u64), blkno ∈ update.addr <$> updlist_olds.*1 ->
                blkno ∈ dom (gmap_addr_by_block σl.(latest)))
          as Hupdlist_olds_σl_latest_blkno.
        {
          intros blkno Hblkno.
          eapply elem_of_list_fmap_2 in Hblkno. destruct Hblkno as [u [? Hblkno]]. subst.
          eapply elem_of_list_fmap_2 in Hblkno. destruct Hblkno as [lv [? Hblkno]]. subst.
          eauto.
        }

        rewrite Hlatestdom.
        rewrite apply_upds_u64_dom; eauto.
        rewrite -Hlatestdom; eauto.
      }

      iIntros (k offmap blk Hoffmap Hblk).
      rewrite /bufDataTs_in_crashblock /bufDataT_in_block.

      destruct (decide (k ∈ update.addr <$> updlist_olds.*1)).
      {
        eapply elem_of_list_fmap_2 in e. destruct e as [u [? Hu]]. subst.
        eapply elem_of_list_fmap_2 in Hu. destruct Hu as [lv [? Hlv]]. subst.
        eapply Hupdlist_olds_σl_latest in Hlv as Hbufamap.
        apply elem_of_dom in Hbufamap. destruct Hbufamap as [bufamap_lv Hbufamap].
        eapply elem_of_list_lookup_1 in Hlv as Hlv'. destruct Hlv' as [lvi Hlv'].
        iDestruct (big_sepML_lookup_l_acc with "Hupdmap") as (blkno bufamap_lv') "Hupdmap_lv"; eauto.
        { rewrite list_lookup_fmap. erewrite Hlv'. done. }
        iDestruct "Hupdmap_lv" as "(%Hbufamap_lv' & [<- %Hkindok] & _)".
        replace (bufamap_lv') with (bufamap_lv) in * by congruence.
        destruct Hkindok as [K [Hkind Hok]].

        iExists _. iSplit; first by iFrame "%".
        iApply big_sepM_forall. iIntros (off bufData HbufData).
        eapply Hlwh_any in Hlv as Hok'. eapply Hok in Hok'.
        rewrite /updOffsetsOK in Hok'.

        eapply Hupdlist_olds_σl_latest in Hlv as Hl.
        eapply elem_of_subseteq in Hl; eauto.
        apply elem_of_dom in Hl. destruct Hl as [offmap'' Hl].
        iDestruct (big_sepM2_lookup_l_some with "Hcrashheap_latest") as (?) "%Hsome"; eauto.
        iDestruct (big_sepM2_lookup with "Hcrashheap_latest") as (K') "(%Hk' & Hpre)"; eauto.
        rewrite Hkind in Hk'; inversion Hk'; clear Hk'; subst.

        iAssert (⌜x2 = latest_update lv.2.1 lv.2.2⌝)%I as %->.
        {
          iNamed "Hlwh_crash_heaps".
          iDestruct (big_sepL_app with "Hpossible_heaps") as "[_ Hlatest_crash_heap]".
          simpl.
          iDestruct ("Hlatest_crash_heap") as "[%Hlatest_crash_heap' _]".
          rewrite Hlatest_crash_heap' in Hsome.
          rewrite /possible app_length /= in Hcrashes_complete.
          rewrite take_ge in Hsome; last by lia.
          erewrite Hlwh_any in Hsome; last by eauto. iPureIntro. congruence.
        }

        iAssert (⌜blk = (lv.1).(update.b)⌝)%I as %->.
        {
          rewrite apply_upds_u64_lookup in Hblk; eauto.
          iPureIntro. congruence.
        }

        erewrite gmap_addr_by_block_union_lookup in Hoffmap; eauto.
        2: {
          rewrite gmap_addr_by_block_fmap lookup_fmap Hbufamap. done. }
        inversion Hoffmap; clear Hoffmap; subst.
        eapply lookup_union_Some_raw in HbufData. destruct HbufData as [HbufData | [Hnone HbufData]].
        {
          assert (is_Some (offmap'' !! off)) as Hoffmap''.
          {
            eapply elem_of_dom.
            eapply gmap_addr_by_block_elem_of_2; eauto.
            eapply elem_of_subseteq; eauto.
            eapply gmap_addr_by_block_elem_of_1; eauto.
            rewrite lookup_fmap in HbufData.
            eapply fmap_Some_1 in HbufData; destruct HbufData; intuition.
            eapply elem_of_dom. eauto.
          }
          destruct Hoffmap'' as [offmap''off Hoffmap''].
          iDestruct (big_sepM_lookup with "Hpre") as "(%Hin & %Hvalidaddr & %Hvalidoff & %Hk')"; eauto.
          iPureIntro.
          destruct offmap''off. simpl in *; subst.
          specialize (Hok' _ b Hvalidaddr Hvalidoff Hin).
          rewrite lookup_fmap in HbufData.
          eapply fmap_Some_1 in HbufData. destruct HbufData as [HbufDataPrev [HbufData ?]]; subst; simpl in *.
          rewrite lookup_fmap HbufData /= in Hok'.
          destruct Hok' as [Hok' ?]; subst.
          intuition eauto.
        }
        {
          iDestruct (big_sepM_lookup with "Hpre") as "(%Hin & %Hvalidaddr & %Hvalidoff & %Hk')"; eauto.
          iPureIntro.
          intuition eauto.
          destruct bufData as [bufDataK bufData]. simpl in *. subst.
          specialize (Hok' _ bufData Hvalidaddr Hvalidoff Hin).
          rewrite lookup_fmap in Hnone. rewrite -> fmap_None in Hnone.
          rewrite lookup_fmap Hnone /= in Hok'.
          eauto.
        }
      }
      {
        rewrite apply_upds_u64_lookup_ne in Hblk; eauto.
        rewrite gmap_addr_by_block_union_lookup_none in Hoffmap.
        2: {
          eapply not_elem_of_dom.
          rewrite gmap_addr_by_block_fmap.
          rewrite dom_fmap_L. eauto.
        }
        iDestruct (big_sepM2_lookup with "Hcrashheap_latest") as "Hcrashheap_latest_k"; eauto.
      }
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
    iApply "HΦ". by iFrame.
  }
  {
    iNamed "Hnpos".
    wp_apply (release_spec with "[$Histxn_lock $Hlocked Hlockedheap Histxn_pos]").
    { iExists _, _, _. iFrame. }

    wp_pures.
    iApply "HΦ". by iFrame.
  }
Unshelve.
  all: eauto.
Qed.

Theorem wp_txn_CommitWait l q γ dinit bufs buflist (bufamap : gmap addr _) (wait : bool) E (PreQ: iProp Σ) (Q : nat -> iProp Σ) :
  {{{ is_txn l γ dinit ∗
      own_slice bufs ptrT q buflist ∗
      ( [∗ maplist] a ↦ buf; bufptrval ∈ bufamap; buflist, is_txn_buf_pre γ bufptrval a buf ) ∗
      PreQ ∧ ( ⌜bufamap ≠ ∅⌝ -∗ |NC={⊤ ∖ ↑walN ∖ ↑invN, E}=>
        ∀ CP,
        □ ( ∀ σl a v,
          ( CP ∗ ghost_var γ.(txn_crashstates) (3/4) σl ∗ pointsto_txn γ a v ) -∗ ⌜σl.(latest) !! a = Some v⌝ ) ∗
        CP
        -∗ |NC={E}=>
        CP ∗
        ∃ (σl : async (gmap addr {K & bufDataT K})),
          "Hcrashstates_frag" ∷ ghost_var γ.(txn_crashstates) (3/4) σl ∗
          "Hcrashstates_fupd" ∷ (
            let σ : gmap addr {K & bufDataT K} := ((λ b, existT _ b.(buf_).(bufData)) <$> bufamap) ∪ latest σl in
            ghost_var γ.(txn_crashstates) (3/4) (async_put σ σl)
            -∗ |NC={E, ⊤ ∖ ↑walN ∖ ↑invN}=> Q (length (possible σl))  ))
  }}}
    Log__CommitWait #l (slice_val bufs) #wait
  {{{ (ok : bool), RET #ok;
      if ok then
        (( ⌜bufamap ≠ ∅⌝ -∗ ∃ (txn_id : nat),
          Q txn_id ∗
          ( ⌜wait=true⌝ -∗ @mono_nat_lb_own Σ _ γ.(txn_walnames).(wal_heap_durable_lb) txn_id ) ) ∗
        ( ⌜bufamap = ∅⌝ -∗ PreQ )) ∗
        [∗ map] a ↦ buf ∈ bufamap,
          pointsto_txn γ a (existT _ buf.(buf_).(bufData))
      else
        PreQ ∗
        ([∗ map] a ↦ buf ∈ bufamap,
          pointsto_txn γ a (existT buf.(buf_).(bufKind) buf.(data_)))
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
  destruct (decide (uint.Z 0 < uint.Z bufs.(Slice.sz))).
  - wp_pures.

    iAssert (⌜ bufamap ≠ ∅ ⌝)%I as "%Hnotempty".
    {
      iIntros (H); subst.
      iDestruct (big_sepML_empty_l with "Hbufpre") as %->.
      iDestruct (own_slice_sz with "Hbufs") as "%Hlen".
      simpl in *; word.
    }

    wp_apply (wp_txn__doCommit _ _ _ _ _ _ _ _ PreQ with "[$Htxn $Hbufs $Hbufpre Hfupd]"); eauto.
    {
      iSplit; [ iDestruct "Hfupd" as "[$ _]" | iRight in "Hfupd" ].
      iMod ("Hfupd" with "[]") as "Hfupd"; first eauto.
      iModIntro.
      iExact "Hfupd".
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
        iApply "HΦ". iModIntro. iFrame.
        iSplitL.
        2: { iIntros "%H". congruence. }
        iIntros (H). iExists _; iFrame.
        done.

      * wp_pures.
        wp_load.
        iApply "HΦ". iModIntro. iFrame.
        iSplitL.
        2: { iIntros "%H". congruence. }
        iIntros (?). iExists _; iFrame. iIntros (?). intuition congruence.

    + wp_apply util_proof.wp_DPrintf.
      wp_store.
      wp_load.
      iApply "HΦ".
      by iFrame.

  - wp_apply util_proof.wp_DPrintf.

    iAssert (⌜ bufamap = ∅ ⌝)%I as "%Hempty".
    { destruct buflist.
      { iDestruct (big_sepML_empty_m with "Hbufpre") as %->. done. }
      iDestruct (own_slice_sz with "Hbufs") as "%Hlen". simpl in *.
      replace (uint.Z 0) with 0 in n by word. word.
    }

    wp_load.
    iApply "HΦ".

    iDestruct (own_slice_sz with "Hbufs") as %Hbuflistlen.
    assert (uint.Z bufs.(Slice.sz) = 0) by (revert n; word).
    assert (length (list.untype buflist) = 0%nat) by len.
    rewrite fmap_length in H0.
    apply length_zero_iff_nil in H0; subst.

    iModIntro.
    iSplit; last by iApply big_sepM_empty.
    iSplitR.
    { iIntros; congruence. }
    iIntros.
    iDestruct "Hfupd" as "[Hpreq _]". iFrame.
Qed.


End goose_lang.
