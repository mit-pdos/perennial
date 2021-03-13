From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import liftable auth_map.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

From Goose.github_com.mit_pdos.goose_nfsd Require Import simple.
From Perennial.program_proof Require Import txn.txn_proof marshal_proof addr_proof crash_lockmap_proof addr.addr_proof buf.buf_proof.
From Perennial.program_proof Require Import buftxn.sep_buftxn_proof.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import NamedProps Map List range_set.
From Perennial.program_logic Require Import spec_assert.
From Perennial.goose_lang.lib Require Import slice.typed_slice into_val.
From Perennial.program_proof Require Import simple.spec simple.invariant simple.common simple.iread.

Section heap.
Context `{!heapG Σ}.
Context `{!simpleG Σ}.
Implicit Types (stk:stuckness) (E: coPset).

Variable P : SimpleNFS.State -> iProp Σ.
Context `{Ptimeless : !forall σ, Timeless (P σ)}.

Opaque nfstypes.READ3res.S.
Opaque slice_val.

Lemma nfstypes_read3res_merge reply s ok fail :
  ( reply ↦[nfstypes.READ3res.S :: "Status"] s ∗
    reply ↦[nfstypes.READ3res.S :: "Resok"] ok ∗
    reply ↦[nfstypes.READ3res.S :: "Resfail"] fail ) -∗
  reply ↦[struct.t nfstypes.READ3res.S]{1} (s, (ok, (fail, #()))).
Proof.
  iIntros "(Status & Resok & Resfail)".
  iApply struct_fields_split. iFrame. done.
Qed.

Theorem wp_NFSPROC3_READ γ (nfs : loc) (fh : u64) (fhslice : Slice.t) (offset : u64) (count : u32) (Q : SimpleNFS.res (bool * SimpleNFS.buf) -> iProp Σ) dinit :
  {{{ is_fs P γ nfs dinit ∗
      is_fh fhslice fh ∗
      ∀ σ σ' r E,
        ⌜relation.denote (SimpleNFS.wrapper fh (SimpleNFS.read fh offset count)) σ σ' r⌝ -∗
        ( P σ ={E}=∗ P σ' ∗ Q r )
  }}}
    Nfs__NFSPROC3_READ #nfs
      (struct.mk_f nfstypes.READ3args.S [
        "File" ::= struct.mk_f nfstypes.Nfs_fh3.S [
          "Data" ::= slice_val fhslice
        ];
        "Offset" ::= #offset;
        "Count" ::= #count
      ])%V
  {{{ v,
      RET v;
      ( ∃ (eof : bool) (databuf : list u8) (dataslice : Slice.t) resok,
        ⌜ getField_f nfstypes.READ3res.S "Status" v = #(U32 0) ⌝ ∗
        ⌜ getField_f nfstypes.READ3res.S "Resok" v = resok ⌝ ∗
        ⌜ getField_f nfstypes.READ3resok.S "Eof" resok = #eof ⌝ ∗
        ⌜ getField_f nfstypes.READ3resok.S "Data" resok = slice_val dataslice ⌝ ∗
        is_slice dataslice u8T 1%Qp databuf ∗
        Q (SimpleNFS.OK (eof, databuf)) ) ∨
      ( ∃ (stat : Z),
        ⌜ getField_f nfstypes.READ3res.S "Status" v = #(U32 stat) ⌝ ∗
        ⌜ stat ≠ 0 ⌝ ∗
        Q SimpleNFS.Err )
  }}}.
Proof using Ptimeless.
  iIntros (Φ) "(Hfs & #Hfh & Hfupd) HΦ".
  iNamed "Hfs".

  wp_call.
  iFreeze "HΦ".
  wp_apply wp_ref_of_zero; first by auto.
  iIntros (reply) "Hreply".
  wp_apply util_proof.wp_DPrintf.
  wp_loadField.
  wp_apply (wp_BufTxn__Begin with "[$Histxn $Htxnsys]").
  iIntros (γtxn buftx) "Hbuftxn".
  wp_apply (wp_fh2ino with "Hfh").
  wp_pures.
  wp_apply (wp_validInum).
  iIntros (valid) "%Hvalid".
  wp_if_destruct.
  { wp_pures.
    wp_apply (wp_storeField_struct with "Hreply"); first by auto.
    iIntros "Hreply".

    (* Simulate to get Q *)
    iApply fupd_wp.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct ("Hfupd" with "[] HP") as "Hfupd".
    {
      iPureIntro.
      simpl.
      monad_simpl.
      simpl.
      destruct (src !! fh) eqn:He.
      { exfalso.
        assert (fh ∈ dom (gset u64) src) as Hin.
        { apply elem_of_dom. rewrite He. eauto. }
        rewrite Hdom in Hin. apply Hvalid in Hin. congruence. }
      rewrite He.
      econstructor. eauto.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    wp_load.
    iThaw "HΦ".
    iApply "HΦ".
    iRight. iExists _.
    iFrame "HQ".
    iPureIntro.
    Transparent nfstypes.READ3res.S.
    simpl. intuition eauto.
    Opaque nfstypes.READ3res.S.
    lia.
  }

  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$Hislm]"); first by intuition eauto.
  iIntros "Hcrashlocked".

  wp_pures.
  wp_bind (NFSPROC3_READ_internal _ _ _ _).
  iApply (wpc_wp _ _ _ _ _ True).

  iDestruct (use_CrashLocked _ 8 with "Hcrashlocked") as "Hcrashuse"; [| lia | iApply "Hcrashuse"].
  { apply _. }
  iSplit.
  { iModIntro. done. }
  iIntros ">Hstable".
  iApply ncfupd_wpc; iSplit.
  {
    iModIntro.
    iMod (is_inode_stable_crash with "Htxncrash Hstable") as "Hcrash".
    iModIntro. iSplit; first done. done.
  }
  iNamed "Hstable".

  iMod (lift_liftable_into_txn with "Hbuftxn Hinode_disk") as "[Hinode_disk Hbuftxn]";
    [ solve_ndisj .. | ].
  iNamed "Hinode_disk".

  iNamed "Hbuftxn".
  iModIntro.

  iApply wpc_cfupd.
  iCache with "Hinode_state Hbuftxn_durable".
  { crash_case.
    iDestruct (is_buftxn_durable_to_old_pred with "Hbuftxn_durable") as "[Hold _]".
    iModIntro.
    iMod (is_inode_crash_prev with "Htxncrash [$Hinode_state $Hold]") as "Hcrash".
    iModIntro.
    iSplit; done.
  }

  wpc_call.
  wpc_bind (NFSPROC3_READ_wp _ _ _ _).
  wpc_frame.
  wp_call.

  wp_apply (wp_ReadInode with "[$Hbuftxn_mem $Hinode_enc]"); first by intuition eauto.
  iIntros (ip) "(Hbuftxn_mem & Hinode_enc & Hinode_mem)".

  wp_apply (wp_Inode__Read with "[$Hbuftxn_mem $Hinode_mem $Hinode_data]").
  iIntros (resSlice eof vs) "(HresSlice & Hbuftxn_mem & Hinode_mem & Hinode_data & %Hvs & %Hvslen & %Heof)".

  iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".

  wp_apply wp_slice_len.
  wp_apply (wp_struct_fieldRef_mapsto with "Resok"); first done.
  iIntros (fl) "[%Hfl Resok]".
  wp_apply (wp_storeField_struct with "Resok").
  { auto. }
  iIntros "Resok".
  rewrite Hfl; clear Hfl fl.

  wp_apply (wp_struct_fieldRef_mapsto with "Resok"); first done.
  iIntros (fl) "[%Hfl Resok]".
  wp_apply (wp_storeField_struct with "Resok").
  { compute. val_ty. }
  iIntros "Resok".
  rewrite Hfl; clear Hfl fl.

  wp_apply (wp_struct_fieldRef_mapsto with "Resok"); first done.
  iIntros (fl) "[%Hfl Resok]".
  wp_apply (wp_storeField_struct with "Resok").
  { compute. val_ty. }
  iIntros "Resok".
  rewrite Hfl; clear Hfl fl.

  iFreeze "Status Resok Resfail".

  iNamed 1.
  wpc_pures.

  iDestruct (is_buftxn_mem_durable with "Hbuftxn_mem Hbuftxn_durable") as "Hbuftxn".

  wpc_apply (wpc_BufTxn__CommitWait with "[$Hbuftxn $Htxncrash Hinode_enc Hinode_data]").
  2-4: try solve_ndisj.
  2: { (* XXX is there a clean version of this? *) generalize (buftxn_maps_to γtxn). intros. iAccu. }
  { typeclasses eauto. }

  iSplit.
  { iModIntro.
    iIntros "[[H _]|[H0 H1]]"; iModIntro; iSplit; try done; iModIntro.
    { iApply is_inode_crash_next. iFrame. }
    { iApply is_inode_crash_next. iFrame "Hinode_state". iRight. iFrame. }
  }

  iModIntro.
  iIntros (ok) "Hcommit".
  destruct ok; subst.
  - (* Simulate to get Q *)
    iApply fupd_wpc.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
    iDestruct (big_sepM_lookup with "Hnooverflow") as %Hnooverflow; eauto.
    iDestruct ("Hfupd" with "[] HP") as "Hfupd".
    {
      iPureIntro.
      simpl.
      monad_simpl.
      simpl.
      rewrite Hsrc_fh.
      simpl.
      eapply relation.bind_runs with (x:=false). { econstructor. auto. }
      simpl.
      monad_simpl.
      econstructor.
      {
        eapply relation.suchThat_runs with (x:=length vs).
        destruct (decide (length vs = 0)) eqn:He; eauto. right.
        rewrite -Hvs. rewrite take_length.
        rewrite drop_length.
        destruct (decide (int.nat offset ≤ length state)); first by lia.
        exfalso.
        rewrite -> drop_ge in Hvs by lia. rewrite take_nil in Hvs.
        subst. simpl in n. congruence.
      }
      monad_simpl.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    wpc_frame "Hinode_state Hcommit".
    { iModIntro.
      iMod (is_inode_crash_prev_own with "Htxncrash [$Hinode_state $Hcommit]") as "H".
      iModIntro. iSplit; done. }

    wp_storeField.
    iNamed 1.

    iSplitR "Hinode_state Hcommit".
    2: {
      iModIntro.
      iExists _; iFrame.
      iExists _; iFrame.
    }
    iIntros "Hcrashlocked".
    iSplit.
    { iModIntro. done. }

    wp_loadField.
    wp_apply (wp_LockMap__Release with "Hcrashlocked").

    wp_apply (wp_LoadAt with "[Status Resok Resfail]").
    { iModIntro. iApply nfstypes_read3res_merge. iThaw "Resok Resfail". iFrame. }
    iIntros "Hreply". simpl.
    iThaw "HΦ".
    iApply "HΦ". iLeft.
    iExists _, _, _, _.
Transparent nfstypes.READ3res.S.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iFrame. iExactEq "HQ".
    assert (length state < 2^64)%Z as Hlenstatebound.
    { eapply Hnooverflow; clear Hnooverflow. }
    clear Hnooverflow.
    assert (int.nat (U64 (Z.of_nat (length state))) = length state) as Hlenstate.
    { word. }
    f_equal. f_equal. f_equal.
    { destruct eof; (intuition idtac);
        destruct (ge_dec (int.nat offset + length vs) (length state)); try reflexivity.
      { lia. }
      { symmetry. eapply H2. lia. }
    }
    { eauto. }

  - (* Simulate to get Q *)
    iApply fupd_wpc.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
    iDestruct ("Hfupd" with "[] HP") as "Hfupd".
    {
      iPureIntro.
      simpl.
      monad_simpl.
      simpl.
      rewrite Hsrc_fh.
      simpl.
      eapply relation.bind_runs with (x:=true). { econstructor. auto. }
      simpl.
      monad_simpl.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    iDestruct "Hcommit" as "[Hcommit _]".
    wpc_frame "Hinode_state Hcommit".
    { iModIntro.
      iMod (is_inode_crash_prev_own with "Htxncrash [$Hinode_state $Hcommit]") as "H".
      iModIntro.
      iSplit; done. }

    wp_storeField.
    iNamed 1.

    iSplitR "Hinode_state Hcommit".
    2: {
      iModIntro.
      iExists _; iFrame.
    }
    iIntros "Hcrashlocked".
    iSplit.
    { iModIntro. done. }

    wp_loadField.
    wp_apply (wp_LockMap__Release with "Hcrashlocked").

    wp_apply (wp_LoadAt with "[Status Resok Resfail]").
    { iModIntro. iApply nfstypes_read3res_merge. iThaw "Resok Resfail". iFrame. }
    iIntros "Hreply".
    iThaw "HΦ".
    iApply "HΦ".
    iRight. iExists _. iFrame "HQ".
    iPureIntro.
    Transparent nfstypes.READ3res.S.
    simpl. intuition eauto.
    Opaque nfstypes.READ3res.S.
    lia.

Unshelve.
  all: eauto.
Qed.

End heap.
