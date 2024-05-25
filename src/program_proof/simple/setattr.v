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

Opaque nfstypes.SETATTR3res.
Opaque slice_val.

Lemma is_inode_data_shrink: forall state blk (u: u64) M,
   ¬ (uint.Z (length state) < uint.Z u)%Z ->
  is_inode_data (length state) blk state M -∗
  is_inode_data (Σ:=Σ) (length (take (uint.nat u) state)) blk (take (uint.nat u) state) M.
Proof.
  iIntros (state blk u γtxn) "%H Hinode_data".
  iNamed "Hinode_data".
  rewrite /is_inode_data.
  iExists bbuf.
  iFrame.
  iPureIntro.
  rewrite -> firstn_length_le by lia.
  split; [ | word ].
  rewrite <- Hdiskdata.
  rewrite take_take.
  auto with f_equal lia.
Qed.

Lemma nfstypes_setattr3res_merge reply s ok fail :
  ( reply ↦[nfstypes.SETATTR3res :: "Status"] s ∗
    reply ↦[nfstypes.SETATTR3res :: "Resok"] ok ∗ 
    reply ↦[nfstypes.SETATTR3res :: "Resfail"] fail ) -∗
  reply ↦[struct.t nfstypes.SETATTR3res] (s, (ok, (fail, #()))).
Proof.
  iIntros "(Status & Resok & Resfail)".
  iApply struct_fields_split. iFrame. done.
Qed.

Theorem wp_NFSPROC3_SETATTR γ (nfs : loc) (fh : u64) (fhslice : Slice.t) (sattr: SimpleNFS.sattr) (Q : SimpleNFS.res unit -> iProp Σ) dinit :
  {{{ is_fs P γ nfs dinit ∗
      is_fh fhslice fh ∗
      ( ∀ σ σ' (r : SimpleNFS.res unit) E,
        ⌜relation.denote (SimpleNFS.wrapper fh (SimpleNFS.setattr fh sattr)) σ σ' r⌝ -∗
        ( P σ -∗ |8={E}=> P σ' ∗ Q r ) )
  }}}
    Nfs__NFSPROC3_SETATTR #nfs
      (struct.mk_f nfstypes.SETATTR3args [
        "Object" ::= struct.mk_f nfstypes.Nfs_fh3 [
          "Data" ::= slice_val fhslice
        ];
        "New_attributes" ::= struct.mk_f nfstypes.Sattr3 [
          "Size" ::= struct.mk_f nfstypes.Set_size3 [
            "Set_it" ::= match sattr.(SimpleNFS.sattr_size) with | None => #false | Some _ => #true end;
            "Size" ::= match sattr.(SimpleNFS.sattr_size) with | None => #0 | Some s => #s end
          ]
        ]
      ])%V
  {{{ v,
      RET v;
      ( ⌜ getField_f nfstypes.SETATTR3res "Status" v = #(W32 0) ⌝ ∗
        Q (SimpleNFS.OK tt) ) ∨
      ( ∃ stat,
        ⌜ getField_f nfstypes.SETATTR3res "Status" v = #(W32 stat) ⌝ ∗
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
    simpl. intuition eauto.
    lia.
  }

  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$Hislm]"); first by intuition eauto.
  iIntros "Hcrashlocked".

  wp_pures.
  wp_bind (NFSPROC3_SETATTR_internal _ _ _ _).

  iApply (wpc_wp _ _ _ _ True).
  iApply (use_CrashLocked _ with "Hcrashlocked"); first by eauto.
  iSplit.
  { done. }
  iIntros "Hstable".
  iApply ncfupd_wpc; iSplit.
  {
    iMod (is_inode_stable_crash with "Htxncrash Hstable") as "H".
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
  wpc_bind (NFSPROC3_SETATTR_wp _ _ _ _).
  wpc_frame.
  wp_call.

  wp_apply (wp_ReadInode with "[$Hjrnl_mem $Hinode_enc]"); first by intuition eauto.
  iIntros (ip) "(Hjrnl_mem & Hinode_enc & Hinode_mem)".

  wp_apply (typed_mem.wp_AllocAt); eauto.
  iIntros (wpok) "Hwpok".

  wp_pures.
  destruct sattr.
  destruct sattr_size; wp_if.
  {
    wp_pures.
    iNamed "Hinode_mem".
    wp_loadField.
    wp_if_destruct.
    {
      wp_loadField.
      wp_apply (wp_NewSlice (V:=u8)).
      iIntros (zeros) "Hzeros".
      wp_loadField. wp_loadField.

      wp_apply (wp_Inode__Write with "[$Hjrnl_mem $Hinum $Hisize $Hidata $Hinode_data $Hinode_enc Hzeros]").
      { iDestruct (own_slice_to_small with "Hzeros") as "$".
        iPureIntro. intuition eauto.
        rewrite replicate_length. done.
      }

      iIntros (wcount ok) "[Hjrnl_mem [(Hinode_mem & Hinode_enc & Hinode_data & %Hok) | Hok]]"; intuition subst.
      {
        iNamed "Hinode_mem".
        wp_loadField.
        wp_pures.

        wp_if_destruct.
        {
          iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
          wp_storeField. wp_load. iModIntro. iNamed 1.

          iApply fupd_wpc.
          iInv "Hsrc" as ">Hopen" "Hclose".
          iNamed "Hopen".
          iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
          iDestruct (big_sepM_lookup with "Hnooverflow") as %Hnooverflow; eauto.
          exfalso.
          revert Heqb. word_cleanup. intros.
          revert H0. rewrite replicate_length. word_cleanup. intros.
          apply Heqb0. rewrite Z.max_r; last by lia. word_cleanup.
          f_equal. f_equal. word.
        }

        {
          wp_store.
          wp_load. iModIntro.

          iNamed 1.
          wpc_pures.
          iDestruct (is_jrnl_mem_durable with "Hjrnl_mem Hjrnl_durable") as "Hjrnl".

          wpc_apply (wpc_Op__CommitWait with "[$Hjrnl $Htxncrash Hinode_enc Hinode_data]").
          5: { (* XXX is there a clean version of this? *) generalize (jrnl_maps_to γtxn). intros. iAccu. }
          2-4: solve_ndisj.
          { typeclasses eauto. }

          iSplit.
          { iIntros "[[H _]|[H0 H1]]".
            { iDestruct (is_inode_crash_next with "[$Hinode_state $H]") as "H".
              iModIntro. iSplit; try (iIntros "? !>"); done. }

            iIntros "C".
            iInv "Hsrc" as ">Hopen" "Hclose".
            iNamed "Hopen".
            iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh2".
            iDestruct (big_sepM_lookup with "Hnooverflow") as %Hnooverflow; eauto.
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
            }
            iMod (map_update with "Hsrcheap Hinode_state") as "[Hsrcheap Hinode_state]".
            iMod "Hfupd" as "[HP HQ]".
            iMod ("Hclose" with "[Hsrcheap HP]").
            { iModIntro. iExists _.  iFrame "∗%#". iSplit.
              { iPureIntro. rewrite /= dom_insert_L. set_solver+ Hdom H5. }
              iDestruct (big_sepM_delete with "Hnooverflow") as "[H0 H1]"; eauto.
              iApply (big_sepM_insert_delete with "[$H1]").
              iPureIntro.
              rewrite app_length replicate_length.
              rewrite replicate_length in H0.
              rewrite take_length_ge.
              2: { revert Heqb. word. }
              revert H0.
              word.
            }
            iModIntro. iSplit; first by done.
            iIntros "? !>".
            iExists _. iFrame. iExists _.

            assert (length state < uint.Z w)%Z by (revert Heqb; word).
            rewrite -> Z.max_r in Heqb0 by word.
            rewrite -Heqb0. word_cleanup.
            rewrite -> Z.max_r by word.
            rewrite !app_length !replicate_length take_length_ge.
            2: word.
            replace (length state + (uint.Z w - length state))%Z with (uint.Z w) by lia.
            replace (length state + (uint.Z w - length state))%Z with (uint.Z w) by lia.
            replace (length state + (uint.nat w - length state)) with (uint.nat w) by lia.
            replace (W64 (uint.nat w)) with (W64 (uint.Z w)) by word. iFrame.
            replace (Z.to_nat (length state)) with (length state) by lia.
            rewrite firstn_all. rewrite (firstn_all2 state); last by lia.
            rewrite drop_ge; last by lia. rewrite app_nil_r.
            rewrite firstn_all2. 2: rewrite replicate_length; lia.
            replace (Z.to_nat (uint.Z w - length state)) with (uint.nat w - length state) by lia.
            iFrame.
          }

          iModIntro.
          iIntros (ok) "Hcommit".
          destruct ok; subst.
          {
            (* Simulate to get Q, write succeeded *)
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
              econstructor. { econstructor. auto. }
              instantiate (3 := false).
              simpl.
              monad_simpl.
            }
            iMod (map_update with "Hsrcheap Hinode_state") as "[Hsrcheap Hinode_state]".
            iMod "Hfupd" as "[HP HQ]".
            iMod ("Hclose" with "[Hsrcheap HP]").
            { iModIntro. iExists _.  iFrame "∗%#". iSplit.
              { iPureIntro. rewrite /= dom_insert_L. set_solver+ Hdom H5. }
              iDestruct (big_sepM_delete with "Hnooverflow") as "[H0 H1]"; eauto.
              iApply (big_sepM_insert_delete with "[$H1]").
              iPureIntro.
              rewrite app_length replicate_length.
              rewrite replicate_length in H0.
              rewrite take_length_ge.
              2: { revert Heqb. word. }
              revert H0.
              word.
            }
            iModIntro.

            iDestruct "Hcommit" as "(Hinode_enc & Hinode_data)".

            wpc_frame "Hinode_state Hinode_enc Hinode_data".
            { iMod (is_inode_crash_prev_own with "Htxncrash [$Hinode_state Hinode_enc Hinode_data]") as "H".
              2: { iModIntro. iSplit; try (iIntros "? !>"); done. }

              iRight.
              assert (length state < uint.Z w)%Z by (revert Heqb; word).
              rewrite -> Z.max_r in Heqb0 by word.
              rewrite -Heqb0. word_cleanup.
              rewrite -> Z.max_r by word.
              rewrite !app_length !replicate_length take_length_ge.
              2: word.
              replace (length state + (uint.Z w - length state))%Z with (uint.Z w) by lia.
              replace (length state + (uint.Z w - length state))%Z with (uint.Z w) by lia.
              replace (length state + (uint.nat w - length state)) with (uint.nat w) by lia.
              replace (W64 (uint.nat w)) with (W64 (uint.Z w)) by word. iFrame.
              replace (Z.to_nat (length state)) with (length state) by lia.
              rewrite firstn_all. rewrite (firstn_all2 state); last by lia.
              rewrite drop_ge; last by lia. rewrite app_nil_r.
              rewrite firstn_all2. 2: rewrite replicate_length; lia.
              replace (Z.to_nat (uint.Z w - length state)) with (uint.nat w - length state) by lia.
              iFrame. }

            iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
            wp_pures.
            wp_storeField.
            wp_pures.

            wp_pures. iModIntro.
            iNamed 1.
            iSplitR "Hinode_state Hinode_enc Hinode_data".
            2: {
              iExists _. iFrame "Hinode_state".
              iExists _.
              assert (length state < uint.Z w)%Z by (revert Heqb; word).
              rewrite -> Z.max_r in Heqb0 by word.
              rewrite -Heqb0. word_cleanup.
              rewrite -> Z.max_r by word.
              rewrite !app_length !replicate_length take_length_ge.
              2: word.
              replace (length state + (uint.Z w - length state))%Z with (uint.Z w) by lia.
              replace (length state + (uint.Z w - length state))%Z with (uint.Z w) by lia.
              replace (length state + (uint.nat w - length state)) with (uint.nat w) by lia.
              replace (W64 (uint.nat w)) with (W64 (uint.Z w)) by word. iFrame.
              replace (Z.to_nat (length state)) with (length state) by lia.
              rewrite firstn_all. rewrite (firstn_all2 state); last by lia.
              rewrite drop_ge; last by lia. rewrite app_nil_r.
              rewrite firstn_all2. 2: rewrite replicate_length; lia.
              replace (Z.to_nat (uint.Z w - length state)) with (uint.nat w - length state) by lia.
              iFrame. }

            iIntros "Hcrashlocked".
            iSplit.
            { done. }

            wp_loadField.
            wp_apply (wp_LockMap__Release with "Hcrashlocked").
            wp_apply (wp_LoadAt with "[Status Resok Resfail]").
            { iModIntro. iApply nfstypes_setattr3res_merge. iFrame. }
            iIntros "Hreply". simpl.
            iThaw "HΦ".
            iApply "HΦ". iLeft.
            iSplit; first done.
            iExactEq "HQ".
            f_equal.
          }

          {
            (* Simulate to get Q, write succeeded *)
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
              econstructor. { econstructor. auto. }
              instantiate (3 := true).
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

            iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
            wp_storeField.

            wp_pures. iModIntro.
            iNamed 1.
            iSplitR "Hinode_state Hcommit".
            2: { iExists _; iFrame. }

            iIntros "Hcrashlocked".
            iSplit; first done.

            wp_loadField.
            wp_apply (wp_LockMap__Release with "Hcrashlocked").
            wp_apply (wp_LoadAt with "[Status Resok Resfail]").
            { iModIntro. iApply nfstypes_setattr3res_merge. iFrame. }
            iIntros "Hreply". simpl.
            iThaw "HΦ".
            iApply "HΦ". iRight.
            iExists _.
            iSplit; first done.
            iFrame.
            iPureIntro. lia.
          }
        }
      }

      {
        iDestruct "Hok" as "(Hinode_mem & Hinode_enc & Hinode_data & %Hok)". intuition subst.
        iNamed "Hinode_mem".
        wp_loadField.
        wp_if_destruct.
        2: lia.

        iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
        wp_storeField.

        (* Simulate to get Q after write failed *)
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
          {
            rewrite He.
            eapply relation.bind_runs with (x:=true). { econstructor. auto. }
            simpl.
            monad_simpl.
          }
          rewrite He.
          econstructor. eauto.
        }
        iMod "Hfupd" as "[HP HQ]".
        iMod ("Hclose" with "[Hsrcheap HP]").
        { iModIntro. iExists _. iFrame "∗%#". }
        iModIntro.

        wp_load. iModIntro.

        iNamed 1.
        wpc_pures.

        (* Implicit transaction abort *)
        iDestruct (is_jrnl_mem_durable with "Hjrnl_mem Hjrnl_durable") as "Hjrnl".
        iDestruct (is_jrnl_to_old_pred with "Hjrnl") as "[Hold _]".

        iSplitR "Hinode_state Hold".
        2: { iModIntro. iExists _. iFrame. }
        iIntros "!> Hcrashlocked".
        iSplit.
        { done. }

        wp_loadField.
        wp_apply (wp_LockMap__Release with "Hcrashlocked").
        wp_apply (wp_LoadAt with "[Status Resok Resfail]").
        { iModIntro. iApply nfstypes_setattr3res_merge. iFrame. }
        iIntros "Hreply". simpl.
        iThaw "HΦ".
        iApply "HΦ". iRight.
        iExists _.
        iSplit; first done.
        iFrame.
        iPureIntro. lia.
      }
    }
    {
      (* shrink inode *)
      wp_storeField.
      wp_apply (wp_Inode__WriteInode with "[$Hjrnl_mem Hinum Hisize Hidata $Hinode_enc]").
      { iFrame. iPureIntro. apply Hvalid; auto. }
      iIntros "(Hjrnl_mem & Hinode_enc & Hinode_mem)".
      wp_pures.
      wp_store.
      wp_load. iModIntro.

      iNamed 1.
      wpc_pures.

      iDestruct (is_jrnl_mem_durable with "Hjrnl_mem Hjrnl_durable") as "Hjrnl".

      wpc_apply (wpc_Op__CommitWait with "[$Hjrnl $Htxncrash Hinode_enc Hinode_data]").
      5: { (* XXX is there a clean version of this? *) generalize (jrnl_maps_to γtxn). intros. iAccu. }
      2-4: solve_ndisj.
      { typeclasses eauto. }

      iSplit.
      { iIntros "[[H _]|[H0 H1]]".
        { iDestruct (is_inode_crash_next with "[$Hinode_state $H]") as "H". iModIntro.
          iSplit; try (iIntros "? !>"); done. }

        iIntros "C".
        iInv "Hsrc" as ">Hopen" "Hclose".
        iNamed "Hopen".
        iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh2".
        iDestruct (big_sepM_lookup with "Hnooverflow") as %Hnooverflow; eauto.
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
        }
        iMod (map_update with "Hsrcheap Hinode_state") as "[Hsrcheap Hinode_state]".
        iMod "Hfupd" as "[HP HQ]".

        assert (uint.nat w - length state = 0).
        1: { revert Heqb. word. }
        rewrite H.
        rewrite replicate_0.
        rewrite app_nil_r.

        iMod ("Hclose" with "[Hsrcheap HP]").
        { iModIntro. iExists _. iFrame "∗%#". iSplit.
          { iPureIntro. rewrite /= dom_insert_L. set_solver+ Hdom Hvalid. }
          iDestruct (big_sepM_delete with "Hnooverflow") as "[H0 H1]"; eauto.
          iApply (big_sepM_insert_delete with "[$H1]").

          iPureIntro.
          rewrite -> firstn_length_le by word.
          word.
        }

        iDestruct (is_inode_crash_next with "[$Hinode_state H0 H1]") as "H".
        2: { iModIntro. iSplit; try (iIntros "? !>"); done. }
        iRight.
        rewrite -> firstn_length_le by word.
        iDestruct (is_inode_data_shrink _ _ w with "H1") as "H1".
        { word. }
        rewrite -> firstn_length_le by word.
        replace (W64 (Z.of_nat (uint.nat w))) with w by word. iFrame.
      }

      iModIntro.
      iIntros (ok) "Hcommit".
      destruct ok; subst.
      {
        (* Simulate to get Q, commit succeeded *)
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
          econstructor. { econstructor. auto. }
          instantiate (3 := false).
          simpl.
          monad_simpl.
        }

        iMod (map_update with "Hsrcheap Hinode_state") as "[Hsrcheap Hinode_state]".
        iMod "Hfupd" as "[HP HQ]".

        assert (uint.nat w - length state = 0).
        1: { revert Heqb. word. }
        rewrite H.
        rewrite replicate_0.
        rewrite app_nil_r.

        iMod ("Hclose" with "[Hsrcheap HP]").
        { iModIntro. iExists _.  iFrame "∗%#". iSplit.
          { iPureIntro. rewrite /= dom_insert_L. set_solver+ Hdom Hvalid. }
          iDestruct (big_sepM_delete with "Hnooverflow") as "[H0 H1]"; eauto.
          iApply (big_sepM_insert_delete with "[$H1]").
          iPureIntro.
          rewrite firstn_length_le.
          all: word.
        }
        iModIntro.

        iDestruct "Hcommit" as "[Hinode_enc Hinode_data]".
        iDestruct (is_inode_data_shrink _ _ w with "Hinode_data") as "Hinode_data"; first by word.

        wpc_frame "Hinode_state Hinode_enc Hinode_data".
        { iMod (is_inode_crash_prev_own with "Htxncrash [$Hinode_state Hinode_enc Hinode_data]") as "H".
          2: { iModIntro. iSplit; try (iIntros "? !>"); done. }
          iRight.
          repeat rewrite -> firstn_length_le by word.
          replace (W64 (Z.of_nat (uint.nat w))) with w by word. iFrame. }

        iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
        wp_storeField.
        wp_pures.

        wp_pures. iModIntro.
        iNamed 1.
        iSplitR "Hinode_state Hinode_enc Hinode_data".
        2: {
          iExists _. iFrame "Hinode_state". iExists _.
          repeat rewrite -> firstn_length_le by word.
          replace (W64 (Z.of_nat (uint.nat w))) with w by word. iFrame. }

        iIntros "Hcrashlocked".
        iSplit.
        { done. }

        wp_loadField.
        wp_apply (wp_LockMap__Release with "Hcrashlocked").
        wp_apply (wp_LoadAt with "[Status Resok Resfail]").

        { iModIntro. iApply nfstypes_setattr3res_merge. iFrame. }
        iIntros "Hreply". simpl.
        iThaw "HΦ".
        iApply "HΦ". iLeft.
        iSplit; first done.
        iExactEq "HQ".
        f_equal.
      }

      {
        (* Simulate to get Q, commit failed *)
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
          econstructor. { econstructor. auto. }
          instantiate (3 := true).
          simpl.
          monad_simpl.
        }
        iMod "Hfupd" as "[HP HQ]".
        iMod ("Hclose" with "[Hsrcheap HP]").
        { iModIntro. iExists _.  iFrame "∗%#". }
        iModIntro.

        iDestruct "Hcommit" as "[Hcommit _]".

        wpc_frame "Hinode_state Hcommit".
        { iMod (is_inode_crash_prev_own with "Htxncrash [$Hinode_state $Hcommit]") as "H".
          iModIntro; iSplit; try (iIntros "? !>"); done. }

        iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
        wp_storeField.

        wp_pures. iModIntro.
        iNamed 1.
        iSplitR "Hinode_state Hcommit".
        2: { iExists _. iFrame. }

        iIntros "Hcrashlocked".
        iSplit.
        { done. }

        wp_loadField.
        wp_apply (wp_LockMap__Release with "Hcrashlocked").
        wp_apply (wp_LoadAt with "[Status Resok Resfail]").

        { iModIntro. iApply nfstypes_setattr3res_merge. iFrame. }
        iIntros "Hreply". simpl.
        iThaw "HΦ".
        iApply "HΦ". iRight.
        iExists _.
        iSplit; first done.
        iFrame.
        iPureIntro. lia.
      }
    }
  }

  wp_store.
  wp_load. iModIntro.

  iNamed 1.
  wpc_pures.

  iDestruct (is_jrnl_mem_durable with "Hjrnl_mem Hjrnl_durable") as "Hjrnl".

  (* Not changing the length at all. *)
  wpc_apply (wpc_Op__CommitWait with "[$Hjrnl $Htxncrash Hinode_enc Hinode_data]").
  5: { (* XXX is there a clean version of this? *) generalize (jrnl_maps_to γtxn). intros. iAccu. }
  { typeclasses eauto. }
  all: try solve_ndisj.

  iSplit.
  { iIntros "[[H _]|[H0 H1]]"; iModIntro; iSplit; try done; try (iIntros "? !>").
    { iApply is_inode_crash_next. iFrame. }
    { iApply is_inode_crash_next. iFrame "Hinode_state". iRight. iFrame. } }

  iModIntro.
  iIntros (ok) "Hcommit".
  destruct ok.
  {
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
      econstructor. { econstructor. auto. }
      instantiate (3 := false).
      simpl.
      monad_simpl.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _.  iFrame "∗%#". }
    iModIntro.

    wpc_frame "Hinode_state Hcommit".
    { iMod (is_inode_crash_prev_own with "Htxncrash [$Hinode_state $Hcommit]") as "H".
      iModIntro. iSplit; try (iIntros "? !>"); done. }

    iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
    wp_storeField.

    wp_pures. iModIntro.
    iNamed 1.
    iSplitR "Hinode_state Hcommit".
    2: {
      iExists _; iFrame.
    }
    iIntros "Hcrashlocked".
    iSplit; first done.

    wp_loadField.
    wp_apply (wp_LockMap__Release with "Hcrashlocked").
    wp_apply (wp_LoadAt with "[Status Resok Resfail]").
    { iModIntro. iApply nfstypes_setattr3res_merge. iFrame. }
    iIntros "Hreply". simpl.
    iThaw "HΦ".
    iApply "HΦ". iLeft.
    iSplit; first done.
    iFrame.
  }

  {
    (* Simulate to get Q, commit failed *)
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
      econstructor. { econstructor. auto. }
      instantiate (3 := true).
      simpl.
      monad_simpl.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _.  iFrame "∗%#". }
    iModIntro.

    iDestruct "Hcommit" as "[Hcommit _]".
    wpc_frame "Hinode_state Hcommit".
    { iMod (is_inode_crash_prev_own with "Htxncrash [$Hinode_state $Hcommit]") as "H".
      iModIntro. iSplit; try (iIntros "? !>"); done. }

    iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
    wp_storeField.

    wp_pures. iModIntro.
    iNamed 1.
    iSplitR "Hinode_state Hcommit".
    2: { iExists _; iFrame. }
    iIntros "Hcrashlocked".
    iSplit; first done.

    wp_loadField.
    wp_apply (wp_LockMap__Release with "Hcrashlocked").
    wp_apply (wp_LoadAt with "[Status Resok Resfail]").
    { iModIntro. iApply nfstypes_setattr3res_merge. iFrame. }
    iIntros "Hreply". simpl.
    iThaw "HΦ".
    iApply "HΦ". iRight. iExists _.
    iSplit; first done.
    iSplit; first done.
    iFrame.
  }
Unshelve.
  all: eauto.
Qed.

End heap.
