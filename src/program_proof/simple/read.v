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
From Perennial.program_proof Require Import simple.spec simple.invariant simple.common simple.iread.

Section heap.
Context `{!heapGS Σ}.
Context `{!simpleG Σ}.
Implicit Types (stk:stuckness) (E: coPset).

Variable P : SimpleNFS.State -> iProp Σ.
Context `{Ptimeless : !forall σ, Timeless (P σ)}.

Opaque nfstypes.READ3res.
Opaque slice_val.

Lemma nfstypes_read3res_merge reply s ok fail :
  ( reply ↦[nfstypes.READ3res :: "Status"] s ∗
    reply ↦[nfstypes.READ3res :: "Resok"] ok ∗
    reply ↦[nfstypes.READ3res :: "Resfail"] fail ) -∗
  reply ↦[struct.t nfstypes.READ3res] (s, (ok, (fail, #()))).
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
      (struct.mk_f nfstypes.READ3args [
        "File" ::= struct.mk_f nfstypes.Nfs_fh3 [
          "Data" ::= slice_val fhslice
        ];
        "Offset" ::= #offset;
        "Count" ::= #count
      ])%V
  {{{ v,
      RET v;
      ( ∃ (eof : bool) (databuf : list u8) (dataslice : Slice.t) resok,
        ⌜ getField_f nfstypes.READ3res "Status" v = #(W32 0) ⌝ ∗
        ⌜ getField_f nfstypes.READ3res "Resok" v = resok ⌝ ∗
        ⌜ getField_f nfstypes.READ3resok "Eof" resok = #eof ⌝ ∗
        ⌜ getField_f nfstypes.READ3resok "Data" resok = slice_val dataslice ⌝ ∗
        own_slice dataslice u8T (DfracOwn 1) databuf ∗
        Q (SimpleNFS.OK (eof, databuf)) ) ∨
      ( ∃ (stat : Z),
        ⌜ getField_f nfstypes.READ3res "Status" v = #(W32 stat) ⌝ ∗
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
  wp_apply (wp_Op__Begin with "[$Histxn $Htxnsys]").
  iIntros (γtxn buftx) "Hjrnl".
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
        assert (fh ∈ dom src) as Hin.
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
    Transparent nfstypes.READ3res.
    simpl. intuition eauto.
    Opaque nfstypes.READ3res.
    lia.
  }

  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$Hislm]"); first by intuition eauto.
  iIntros "Hcrashlocked".

  wp_pures.
  wp_bind (NFSPROC3_READ_internal _ _ _ _).
  iApply (wpc_wp _ _ _ _ True).

  iDestruct (use_CrashLocked _ with "Hcrashlocked") as "Hcrashuse"; last iApply "Hcrashuse".
  { rewrite //=. }
  iSplit; first done.
  iIntros "Hstable".
  iApply ncfupd_wpc; iSplit.
  {
    iMod (is_inode_stable_crash with "Htxncrash Hstable") as "Hcrash".
    iModIntro. iSplit; first done. iIntros "_ !>"; done.
  }
  iNamed "Hstable".

  iMod (lift_liftable_into_txn with "Hjrnl Hinode_disk") as "[Hinode_disk Hjrnl]";
    [ solve_ndisj .. | ].
  iNamed "Hinode_disk".

  iNamed "Hjrnl".
  iModIntro.

  iApply wpc_cfupd.
  iCache with "Hinode_state Hjrnl_durable".
  { crash_case.
    iDestruct (is_jrnl_durable_to_old_pred with "Hjrnl_durable") as "[Hold _]".
    iMod (is_inode_crash_prev with "Htxncrash [$Hinode_state $Hold]") as "Hcrash".
    iModIntro. iSplit; first done. iIntros "_ !>"; done.
  }

  wpc_call.
  wpc_bind (NFSPROC3_READ_wp _ _ _ _).
  wpc_frame.
  wp_call.

  wp_apply (wp_ReadInode with "[$Hjrnl_mem $Hinode_enc]"); first by intuition eauto.
  iIntros (ip) "(Hjrnl_mem & Hinode_enc & Hinode_mem)".

  wp_apply (wp_Inode__Read with "[$Hjrnl_mem $Hinode_mem $Hinode_data]").
  iIntros (resSlice eof vs) "(HresSlice & Hjrnl_mem & Hinode_mem & Hinode_data & %Hvs & %Hvslen & %Heof)".

  iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".

  wp_apply wp_slice_len.
  wp_apply (wp_struct_fieldRef_pointsto with "Resok"); first done.
  iIntros (fl) "[%Hfl Resok]".
  wp_apply (wp_storeField_struct with "Resok").
  { auto. }
  iIntros "Resok".
  rewrite Hfl; clear Hfl fl.

  wp_apply (wp_struct_fieldRef_pointsto with "Resok"); first done.
  iIntros (fl) "[%Hfl Resok]".
  wp_apply (wp_storeField_struct with "Resok").
  { compute. val_ty. }
  iIntros "Resok".
  rewrite Hfl; clear Hfl fl.

  wp_apply (wp_struct_fieldRef_pointsto with "Resok"); first done.
  iIntros (fl) "[%Hfl Resok]".
  wp_apply (wp_storeField_struct with "Resok").
  { compute. val_ty. }
  iIntros "Resok".
  rewrite Hfl; clear Hfl fl.

  iFreeze "Status Resok Resfail".

  wp_pures. iModIntro.
  iNamed 1.
  wpc_pures.

  iDestruct (is_jrnl_mem_durable with "Hjrnl_mem Hjrnl_durable") as "Hjrnl".

  wpc_apply (wpc_Op__CommitWait with "[$Hjrnl $Htxncrash Hinode_enc Hinode_data]").
  2-4: try solve_ndisj.
  2: { (* XXX is there a clean version of this? *) generalize (jrnl_maps_to γtxn). intros. iAccu. }
  { typeclasses eauto. }

  iSplit.
  { iIntros "[[H _]|[H0 H1]]"; iModIntro; iSplit; try done; iIntros "_ !>".
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
        destruct (decide (uint.nat offset ≤ length state)); first by lia.
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
    { iMod (is_inode_crash_prev_own with "Htxncrash [$Hinode_state $Hcommit]") as "H".
      iModIntro. iSplit; try done; iIntros "_ !>"; done. }

    wp_storeField.
    wp_pures. iModIntro.
    iNamed 1.

    iSplitR "Hinode_state Hcommit".
    2: {
      iExists _; iFrame.
    }
    iIntros "Hcrashlocked".
    iSplit.
    { done. }

    wp_loadField.
    wp_apply (wp_LockMap__Release with "Hcrashlocked").

    wp_apply (wp_LoadAt with "[Status Resok Resfail]").
    { iModIntro. iApply nfstypes_read3res_merge. iThaw "Resok Resfail". iFrame. }
    iIntros "Hreply". simpl.
    iThaw "HΦ".
    iApply "HΦ". iLeft.
    iExists _, _, _, _.
Transparent nfstypes.READ3res.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iFrame. iExactEq "HQ".
    assert (length state < 2^64)%Z as Hlenstatebound.
    { eapply Hnooverflow; clear Hnooverflow. }
    clear Hnooverflow.
    assert (uint.nat (W64 (Z.of_nat (length state))) = length state) as Hlenstate.
    { word. }
    f_equal. f_equal. f_equal.
    { destruct eof; (intuition idtac);
        destruct (ge_dec (uint.nat offset + length vs) (length state)); try reflexivity.
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
    { iMod (is_inode_crash_prev_own with "Htxncrash [$Hinode_state $Hcommit]") as "H".
      iModIntro. iSplit; first done. iIntros "_ !>"; done. }
    wp_storeField.
    wp_pures. iModIntro. 
    iNamed 1.

    iSplitR "Hinode_state Hcommit".
    2: {
      iExists _; iFrame.
    }
    iIntros "Hcrashlocked".
    iSplit.
    { done. }

    wp_loadField.
    wp_apply (wp_LockMap__Release with "Hcrashlocked").

    wp_apply (wp_LoadAt with "[Status Resok Resfail]").
    { iModIntro. iApply nfstypes_read3res_merge. iThaw "Resok Resfail". iFrame. }
    iIntros "Hreply".
    iThaw "HΦ".
    iApply "HΦ".
    iRight. iExists _. iFrame "HQ".
    iPureIntro.
    Transparent nfstypes.READ3res.
    simpl. intuition eauto.
    Opaque nfstypes.READ3res.
    lia.

Unshelve.
  all: eauto.
Qed.

End heap.
