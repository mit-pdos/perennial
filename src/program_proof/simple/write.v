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
From Perennial.program_proof Require Import simple.spec simple.invariant simple.common simple.iread simple.iwrite.

Section heap.
Context `{!heapGS Σ}.
Context `{!simpleG Σ}.
Implicit Types (stk:stuckness) (E: coPset).

Variable P : SimpleNFS.State -> iProp Σ.
Context `{Ptimeless : !forall σ, Timeless (P σ)}.

Opaque nfstypes.WRITE3res.
Opaque slice_val.

Lemma nfstypes_write3res_merge reply s ok fail :
  ( reply ↦[nfstypes.WRITE3res :: "Status"] s ∗
    reply ↦[nfstypes.WRITE3res :: "Resok"] ok ∗ 
    reply ↦[nfstypes.WRITE3res :: "Resfail"] fail ) -∗
  reply ↦[struct.t nfstypes.WRITE3res]{1} (s, (ok, (fail, #()))).
Proof.
  iIntros "(Status & Resok & Resfail)".
  iApply struct_fields_split. iFrame. done.
Qed.

Theorem wp_NFSPROC3_WRITE γ (nfs : loc) (fh : u64) (fhslice : Slice.t) (offset : u64) (dataslice : Slice.t) (databuf : list u8) (Q : SimpleNFS.res u32 -> iProp Σ) (stab : u32) dinit :
  {{{ is_fs P γ nfs dinit ∗
      is_fh fhslice fh ∗
      is_slice dataslice u8T 1%Qp databuf ∗
      ⌜ (length databuf < 2^32)%Z ⌝ ∗
      ( ∀ σ σ' (r : SimpleNFS.res u32) E,
        ⌜relation.denote (SimpleNFS.wrapper fh (SimpleNFS.write fh offset databuf)) σ σ' r⌝ -∗
        ( P σ -∗ |={E}=> P σ' ∗ Q r ) )
  }}}
    Nfs__NFSPROC3_WRITE #nfs
      (struct.mk_f nfstypes.WRITE3args [
        "File" ::= struct.mk_f nfstypes.Nfs_fh3 [
          "Data" ::= slice_val fhslice
        ];
        "Offset" ::= #offset;
        "Count" ::= #(U32 (length databuf));
        "Stable" ::= #stab;
        "Data" ::= (slice_val dataslice)
      ])%V
  {{{ v,
      RET v;
      ( ∃ (count : u32) resok,
        ⌜ getField_f nfstypes.WRITE3res "Status" v = #(U32 0) ⌝ ∗
        ⌜ getField_f nfstypes.WRITE3res "Resok" v = resok ⌝ ∗
        ⌜ getField_f nfstypes.WRITE3resok "Count" resok = #count ⌝ ∗
        Q (SimpleNFS.OK count) ) ∨
      ( ∃ (stat : Z),
        ⌜ getField_f nfstypes.WRITE3res "Status" v = #(U32 stat) ⌝ ∗
        ⌜ stat ≠ 0 ⌝ ∗
        Q SimpleNFS.Err )
  }}}.
Proof using Ptimeless.
  iIntros (Φ) "(Hfs & #Hfh & Hdata & %Hdatalenbound & Hfupd) HΦ".
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
  wp_apply util_proof.wp_DPrintf.
  wp_apply (wp_validInum).
  iIntros (valid) "%Hvalid".
  wp_if_destruct.
  { wp_apply (wp_storeField_struct with "Hreply"); first by auto.
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
    iApply "HΦ".
    iRight. iExists _.
    iFrame "HQ".
    iPureIntro.
    simpl. intuition eauto.
    lia.
  }

  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$Hislm]"); first by intuition eauto.
  iIntros "Hcrashlocked".

  wp_pures.
  wp_bind (NFSPROC3_WRITE_internal _ _ _ _).

  iApply (wpc_wp _ _ _ _ _ True).
  iApply (use_CrashLocked _ with "Hcrashlocked").
  { eauto. }
  iSplit.
  { done. }
  iIntros "Hstable".
  iApply ncfupd_wpc; iSplit.
  {
    iMod (is_inode_stable_crash with "Htxncrash Hstable") as "Hcrash".
    iModIntro. iSplit; try (iIntros "? !>"); done.
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
    iMod (is_inode_crash_prev with "Htxncrash [$Hinode_state $Hold]") as "H".
    iModIntro. iSplit; try (iIntros "? !>"); done.
  }

  wpc_call.
  wpc_bind (NFSPROC3_WRITE_wp _ _ _ _).
  wpc_frame.
  wp_call.

  wp_apply (wp_ReadInode with "[$Hjrnl_mem $Hinode_enc]"); first by intuition eauto.
  iIntros (ip) "(Hjrnl_mem & Hinode_enc & Hinode_mem)".

  wp_apply (wp_Inode__Write with "[$Hjrnl_mem $Hinode_mem $Hinode_data $Hinode_enc Hdata]").
  { iDestruct (is_slice_to_small with "Hdata") as "$".
    iPureIntro. intuition eauto.
    rewrite /u32_to_u64. word.
  }

  iIntros (wcount ok) "[Hjrnl_mem [(Hinode_mem & Hinode_enc & Hinode_data & %Hok) | Hok]]"; intuition subst.
  {
    wp_pures.

    iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".

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

    wp_pures. iModIntro.
    iNamed 1.
    wpc_pures.

    iDestruct (is_jrnl_mem_durable with "Hjrnl_mem Hjrnl_durable") as "Hjrnl".

    iApply fupd_wpc.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
    iDestruct (big_sepM_lookup with "Hnooverflow") as %Hnooverflow; eauto.
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro. iClear "Hnooverflow".

    replace (int.Z (length state)
              `max` (int.Z offset + int.Z (u32_to_u64 (U32 (length databuf)))))%Z
      with (length (take (int.nat offset) state ++
                    databuf ++ drop (int.nat offset + length databuf) state) : Z).
    2: {
      rewrite /u32_to_u64. word_cleanup.
      destruct (decide (int.Z offset + length databuf ≤ length state)%Z).
      { rewrite Z.max_l; last by lia.
        rewrite !app_length. rewrite drop_length.
        rewrite take_length_le; lia. }
      { rewrite Z.max_r; last by lia.
        rewrite !app_length. rewrite drop_length.
        rewrite take_length_le; try lia.
        revert H3. word. }
    }
    rewrite /u32_to_u64. word_cleanup.
    rewrite (firstn_all2 databuf); last by lia.
    replace (Z.to_nat (length databuf)) with (length databuf) by lia.

    wpc_apply (wpc_Op__CommitWait with "[$Hjrnl $Htxncrash Hinode_enc Hinode_data]").
    5: { (* XXX is there a clean version of this? *) generalize (jrnl_maps_to γtxn). intros. iAccu. }
    2-4: solve_ndisj.
    { typeclasses eauto. }

    iSplit.
    { iIntros "[[H _]|[H0 H1]]".
      { iModIntro. iSplit; first by done. iIntros "? !>".
        iApply is_inode_crash_next. iFrame. }

      iIntros "C".
      iInv "Hsrc" as ">Hopen" "Hclose".
      iNamed "Hopen".
      iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh2".
      iDestruct ("Hfupd" with "[] HP") as "Hfupd".
      {
        iPureIntro.
        simpl.
        monad_simpl.
        simpl.
        rewrite Hsrc_fh2.
        simpl.
        eapply relation.bind_runs with (x:=false). { econstructor. auto. }
        simpl.
        monad_simpl.
        rewrite /ifThenElse.
        rewrite -> decide_True by (move: H3; word).
        simpl.
        monad_simpl.
      }
      iMod (map_update with "Hsrcheap Hinode_state") as "[Hsrcheap Hinode_state]".
      iMod "Hfupd" as "[HP HQ]".
      iMod ("Hclose" with "[Hsrcheap HP]").
      { iModIntro. iExists _. iFrame "∗%#". iSplit.
        { iPureIntro. rewrite /= dom_insert_L. set_solver+ Hdom0 H5. }
        iDestruct (big_sepM_delete with "Hnooverflow") as "[H0 H1]"; eauto.
        iApply (big_sepM_insert_delete with "[$H1]").
        iPureIntro.
        rewrite !app_length drop_length.
        rewrite take_length_le.
        2: { revert H3. word. }
        lia.
      }
      iModIntro. iSplit; first by done.
      iIntros "? !>".
      iApply is_inode_crash_next. iFrame "Hinode_state". iRight. iFrame.
    }

    iModIntro.
    iIntros (ok) "Hcommit".
    destruct ok; subst.
    { (* Simulate to get Q *)
      iApply fupd_wpc.
      iInv "Hsrc" as ">Hopen" "Hclose".
      iNamed "Hopen".
      iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh2".

      iDestruct ("Hfupd" with "[] HP") as "Hfupd".
      {
        iPureIntro.
        simpl.
        monad_simpl.
        simpl.
        rewrite Hsrc_fh2.
        simpl.
        eapply relation.bind_runs with (x:=false). { econstructor. auto. }
        simpl.
        monad_simpl.
        rewrite /ifThenElse.
        rewrite -> decide_True by (move: H3; word).
        simpl.
        monad_simpl.
      }
      iMod (map_update with "Hsrcheap Hinode_state") as "[Hsrcheap Hinode_state]".
      iMod "Hfupd" as "[HP HQ]".
      iMod ("Hclose" with "[Hsrcheap HP]").
      { iModIntro. iExists _. iFrame "∗%#". iSplit.
        { iPureIntro. rewrite /= dom_insert_L. set_solver+ Hdom0 H5. }
        iDestruct (big_sepM_delete with "Hnooverflow") as "[H0 H1]"; eauto.
        iApply (big_sepM_insert_delete with "[$H1]").
        iPureIntro.
        rewrite !app_length drop_length.
        rewrite take_length_le.
        2: { revert H3. word. }
        lia.
      }
      iModIntro.

      wpc_frame "Hinode_state Hcommit".
      { iMod (is_inode_crash_prev_own with "Htxncrash [$Hinode_state $Hcommit]") as "H".
        iModIntro. iSplit; try (iIntros "? !>"); done. }

      wp_storeField.
      iNamed 1.

      iSplitR "Hinode_state Hcommit".
      2: {
        iExists _. iFrame "Hinode_state".
        iDestruct "Hcommit" as "(Hinode_enc & Hinode_data)".
        iExists _. iFrame.
      }
      iIntros "Hcrashlocked".
      iSplit.
      { done. }

      wp_loadField.
      wp_apply (wp_LockMap__Release with "Hcrashlocked").

      wp_apply (wp_LoadAt with "[Status Resok Resfail]").
      { iModIntro. iApply nfstypes_write3res_merge. iFrame. }
      iIntros "Hreply". simpl.
      iApply "HΦ". iLeft.
      iExists _, _.
      iSplit; first done.
      iSplit; first done.
      iSplit; first done.
      iExactEq "HQ".
      f_equal. f_equal. rewrite /u32_from_u64 /u32_to_u64. word.
    }

    { (* Simulate to get Q *)
      iApply fupd_wpc.
      iInv "Hsrc" as ">Hopen" "Hclose".
      iNamed "Hopen".
      iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh2".

      iDestruct ("Hfupd" with "[] HP") as "Hfupd".
      {
        iPureIntro.
        simpl.
        monad_simpl.
        simpl.
        rewrite Hsrc_fh2.
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

      wp_apply (wp_LoadAt with "[Status Resok Resfail]").
      { iModIntro. iApply nfstypes_write3res_merge. iFrame. }
      iIntros "Hreply". simpl.
      iApply "HΦ". iRight.
      iExists _.
      iSplit; first done.
      iFrame.
      iPureIntro. lia.
    }
  }

  {
    iDestruct "Hok" as "(Hinode_mem & Hinode_enc & Hinode_data & %Hok)". intuition subst.
    iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
    wp_storeField. iModIntro.
    iNamed 1.

    iDestruct (is_jrnl_mem_durable with "Hjrnl_mem Hjrnl_durable") as "Hjrnl".

    (* Implicit transaction abort *)
    iDestruct (is_jrnl_to_old_pred with "Hjrnl") as "[Hold _]".

    (* Simulate to get Q *)
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

    wpc_pures.
    { iMod (is_inode_crash_prev_own with "Htxncrash [$Hinode_state $Hold]") as "H".
      iModIntro. iSplit; try (iIntros "? !>"); done. }

    iSplitR "Hinode_state Hold".
    2: {
      iModIntro.
      iExists _; iFrame.
    }
    iIntros "!> Hcrashlocked".
    iSplit; first done.

    wp_loadField.
    wp_apply (wp_LockMap__Release with "Hcrashlocked").

    wp_apply (wp_LoadAt with "[Status Resok Resfail]").
    { iModIntro. iApply nfstypes_write3res_merge. iFrame. }
    iIntros "Hreply". simpl.
    iApply "HΦ". iRight.
    iExists _.
    iSplit; first done.
    iFrame.
    iPureIntro. lia.
  }

Unshelve.
  all: eauto.
  all: try exact 0.
Qed.

End heap.
