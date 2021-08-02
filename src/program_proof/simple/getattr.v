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

Opaque nfstypes.GETATTR3res.
Opaque slice_val.

Theorem wp_Inode__MkFattr ip inum len blk :
  {{{
      is_inode_mem ip inum len blk
  }}}
    Inode__MkFattr #ip
  {{{ fattr3, RET fattr3;
      is_inode_mem ip inum len blk ∗
      ⌜ getField_f nfstypes.Fattr3 "Size" fattr3 = #len ⌝ ∗
      ⌜ getField_f nfstypes.Fattr3 "Fileid" fattr3 = #inum ⌝ ∗
      ⌜ val_ty fattr3 (struct.t nfstypes.Fattr3) ⌝
  }}}.
Proof.
  iIntros (Φ) "Hmem HΦ".
  wp_call.
  iNamed "Hmem".
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_pures.
  iApply "HΦ". iModIntro.
  iSplit.
  { iFrame. }
  iPureIntro; simpl. eauto.
Qed.

Theorem wp_rootFattr :
  {{{ True
  }}}
    rootFattr #()
  {{{ fattr3, RET fattr3;
      ⌜ getField_f nfstypes.Fattr3 "Size" fattr3 = #0 ⌝ ∗
      ⌜ val_ty fattr3 (struct.t nfstypes.Fattr3) ⌝
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  iApply "HΦ". eauto.
Qed.

Lemma nfstypes_getattr3res_merge reply s ok :
  ( reply ↦[nfstypes.GETATTR3res :: "Status"] s ∗
    reply ↦[nfstypes.GETATTR3res :: "Resok"] ok ) -∗
  reply ↦[struct.t nfstypes.GETATTR3res]{1} (s, (ok, #())).
Proof.
  iIntros "(Status & Resok)".
  iApply struct_fields_split. iFrame. done.
Qed.

Theorem wp_NFSPROC3_GETATTR γ (nfs : loc) (fh : u64) (fhslice : Slice.t) (Q : SimpleNFS.res SimpleNFS.fattr -> iProp Σ) dinit :
  {{{ is_fs P γ nfs dinit ∗
      is_fh fhslice fh ∗
      ∀ σ σ' r E,
        ⌜relation.denote (SimpleNFS.full_getattr fh) σ σ' r⌝ -∗
        ( P σ ={E}=∗ P σ' ∗ Q r )
  }}}
    Nfs__NFSPROC3_GETATTR #nfs
      (struct.mk_f nfstypes.GETATTR3args [
        "Object" ::= struct.mk_f nfstypes.Nfs_fh3 [
          "Data" ::= slice_val fhslice
        ]
      ])%V
  {{{ v,
      RET v;
      ( ∃ (sz : u64) resok fattr3,
        ⌜ getField_f nfstypes.GETATTR3res "Status" v = #(U32 0) ⌝ ∗
        ⌜ getField_f nfstypes.GETATTR3res "Resok" v = resok ⌝ ∗
        ⌜ getField_f nfstypes.GETATTR3resok "Obj_attributes" resok = fattr3 ⌝ ∗
        ⌜ getField_f nfstypes.Fattr3 "Size" fattr3 = #sz ⌝ ∗
        Q (SimpleNFS.OK (SimpleNFS.Build_fattr sz)) ) ∨
      ( ∃ (stat : Z),
        ⌜ getField_f nfstypes.GETATTR3res "Status" v = #(U32 stat) ⌝ ∗
        ⌜ stat ≠ 0 ⌝ ∗
        Q SimpleNFS.Err )
  }}}.
Proof using Ptimeless.
  iIntros (Φ) "(Hfs & #Hfh & Hfupd) HΦ".
  iNamed "Hfs".

  wp_call.
  wp_apply wp_ref_of_zero; first by auto.
  iIntros (reply) "Hreply".
  wp_apply util_proof.wp_DPrintf.
  wp_loadField.
  wp_apply (wp_Op__Begin with "[$Histxn $Htxnsys]").
  iIntros (γtxn buftx) "Hjrnl".
  wp_apply (wp_fh2ino with "Hfh").
  wp_pures.
  wp_if_destruct.
  {
    wp_apply (wp_storeField_struct with "Hreply"); first by auto. iIntros "Hreply".

    (* Simulate to get Q *)
    iApply fupd_wp.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct ("Hfupd" with "[] HP") as "Hfupd".
    {
      iPureIntro.
      rewrite /SimpleNFS.full_getattr.
      case_decide as cond; try congruence.
      econstructor. { econstructor. eauto. }
      simpl.
      monad_simpl.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    wp_apply wp_rootFattr. iIntros (fattr3) "(%Hlen & %Hfattr3)".

    iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".

    wp_apply (wp_struct_fieldRef_mapsto with "Resok"); first done.
    iIntros (fl) "[%Hfl Resok]".
    wp_apply (wp_storeField_struct with "Resok").
    { eauto. }
    iIntros "Resok".
    rewrite Hfl; clear Hfl fl.

    wp_apply (wp_LoadAt with "[Status Resok]").
    { iModIntro. iApply nfstypes_getattr3res_merge. iFrame. }
    iIntros "Hreply".

    iApply "HΦ". iLeft. iExists _, _, _.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iFrame.
  }

  wp_apply (wp_validInum).
  iIntros (valid) "%Hvalid".
  wp_if_destruct.
  {
    wp_apply (wp_storeField_struct with "Hreply"); first by auto. iIntros "Hreply".

    (* Simulate to get Q *)
    iApply fupd_wp.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct ("Hfupd" with "[] HP") as "Hfupd".
    {
      iPureIntro.
      rewrite /SimpleNFS.full_getattr.
      case_decide as cond; try congruence.
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
    iApply "HΦ".
    iRight. iExists _.
    iFrame "HQ".
    iPureIntro.
    Transparent nfstypes.GETATTR3res.
    simpl. intuition eauto.
    Opaque nfstypes.GETATTR3res.
    lia.
  }

  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$Hislm]"); first by intuition eauto.
  iIntros "Hcrashlocked".

  wp_pures.
  wp_bind (NFSPROC3_GETATTR_internal _ _ _ _).

  iApply (wpc_wp _ _ _ _ _ True).
  iApply (use_CrashLocked _ with "Hcrashlocked"); first by eauto.
  iSplit.
  { done. }
  iIntros "Hstable".
  iApply ncfupd_wpc; iSplit.
  {
    iMod (is_inode_stable_crash with "Htxncrash Hstable") as "Hcrash".
    iModIntro. iSplit; try (iIntros "? !>"); done.
  }
  iNamed "Hstable".

  iMod (lift_liftable_into_txn with "Hjrnl Hinode_disk") as "[Hinode_disk Hjrnl]".
  { solve_ndisj. }
  { solve_ndisj. }
  { solve_ndisj. }
  iNamed "Hinode_disk".

  iNamed "Hjrnl".
  iModIntro.

  iApply wpc_cfupd.
  iCache with "Hinode_state Hjrnl_durable".
  { crash_case.
    iDestruct (is_jrnl_durable_to_old_pred with "Hjrnl_durable") as "[Hold _]".
    iMod (is_inode_crash_prev with "Htxncrash [$Hinode_state $Hold]") as "H".
    iModIntro. iSplit; try (iIntros "? !>"); done.
  }

  wpc_call.
  wpc_bind (NFSPROC3_GETATTR_wp _ _ _ _).
  wpc_frame.
  wp_call.

  wp_apply (wp_ReadInode with "[$Hjrnl_mem $Hinode_enc]"); first by intuition eauto.
  iIntros (ip) "(Hjrnl_mem & Hinode_enc & Hinode_mem)".

  wp_apply (wp_Inode__MkFattr with "Hinode_mem").
  iIntros (fattr3) "(Hinode_mem & % & % & %)".

  iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".

  wp_apply (wp_struct_fieldRef_mapsto with "Resok"); first done.
  iIntros (fl) "[%Hfl Resok]".
  wp_apply (wp_storeField_struct with "Resok").
  { eauto. }
  iIntros "Resok".
  rewrite Hfl; clear Hfl fl.

  iNamed 1.
  wpc_pures.

  iDestruct (is_jrnl_mem_durable with "Hjrnl_mem Hjrnl_durable") as "Hjrnl".

  wpc_apply (wpc_Op__CommitWait with "[$Hjrnl $Htxncrash Hinode_enc Hinode_data]").
  5: { (* XXX is there a clean version of this? *) generalize (jrnl_maps_to γtxn). intros. iAccu. }
  all: try solve_ndisj.
  { typeclasses eauto. }

  iSplit.
  { iIntros "[[H _]|[H0 H1]]"; iModIntro; iSplit; try done; iIntros "? !>".
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
      rewrite /SimpleNFS.full_getattr.
      case_decide as cond; try congruence.
      simpl.
      monad_simpl.
      rewrite /= Hsrc_fh /=.
      eapply relation.bind_runs with (x:=false). { econstructor. auto. }
      simpl.
      monad_simpl.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    wpc_frame "Hinode_state Hcommit".
    { iMod (is_inode_crash_prev_own with "Htxncrash [$Hinode_state $Hcommit]") as "H".
      iModIntro. iSplit; try (iIntros "? !>"); done. }

    wp_storeField.
    iNamed 1.

    iSplitR "Hinode_state Hcommit".
    2: {
      iExists _; iFrame.
      iExists _; iFrame.
    }
    iIntros "Hcrashlocked".
    iSplit.
    { done. }

    wp_loadField.
    wp_apply (wp_LockMap__Release with "Hcrashlocked").

    wp_apply (wp_LoadAt with "[Status Resok]").
    { iModIntro. iApply nfstypes_getattr3res_merge. iFrame. }
    iIntros "Hreply". simpl.
    iApply "HΦ". iLeft.
    iExists _, _, _.
Transparent nfstypes.GETATTR3res.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iFrame.

  - (* Simulate to get Q *)
    iApply fupd_wpc.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
    iDestruct ("Hfupd" with "[] HP") as "Hfupd".
    {
      iPureIntro.
      rewrite /SimpleNFS.full_getattr.
      case_decide as cond; try congruence.
      simpl.
      monad_simpl.
      simpl.
      rewrite Hsrc_fh.
      simpl.
      eapply relation.bind_runs with (x:=true). { econstructor. auto. }
      econstructor. auto.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    iDestruct "Hcommit" as "[Hcommit _]".
    wpc_frame "Hinode_state Hcommit".
    { iMod (is_inode_crash_prev_own with "Htxncrash [$Hinode_state $Hcommit]") as "H".
      iModIntro. iSplit; try (iIntros "? !>"); done. }

    wp_storeField.
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

    wp_apply (wp_LoadAt with "[Status Resok]").
    { iModIntro. iApply nfstypes_getattr3res_merge. iFrame. }
    iIntros "Hreply".
    iApply "HΦ".
    iRight. iExists _. iFrame "HQ".
    iPureIntro.
    simpl. intuition eauto.
    lia.
Unshelve.
  all: eauto.
  all: try exact O.
Qed.

End heap.
