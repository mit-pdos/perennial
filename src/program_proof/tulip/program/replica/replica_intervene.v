From Perennial.program_proof.tulip.invariance Require Import execute advance.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof Require Import std_proof.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_lowest_rank replica_advance replica_log.
From Perennial.program_proof.tulip.program.backup Require Import
  btcoord_repr btcoord_finalize start.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__intervene
    (rp : loc) (tsW : u64) (ptgsP : Slice.t) (ptgs : txnptgs) rid gid proph γ α :
    let ts := uint.nat tsW in
    is_lnrz_tid γ ts -∗
    is_txnptgs_in_slice ptgsP ptgs -∗
    safe_backup_txn γ ts ptgs -∗
    is_replica_gid_rid rp gid rid -∗
    is_replica_gaddrm rp γ -∗
    is_replica_proph rp proph -∗
    know_tulip_inv_with_proph γ proph -∗
    know_replica_file_inv γ gid rid -∗
    {{{ own_replica rp gid rid γ α }}}
      Replica__intervene #rp #tsW (to_val ptgsP)
    {{{ RET #(); own_replica rp gid rid γ α }}}.
  Proof.
    iIntros (ts) "#Hlnrzed #Hptgs #Hsafebk #Hgidrid #Hgaddrm #Hproph #Hinv #Hinvfile".
    iIntros (Φ) "!> Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) intervene(ts uint64, ptgs []uint64) {                @*)
    (*@     var rank uint64 = 2                                                 @*)
    (*@                                                                         @*)
    wp_pures.
    wp_apply (wp_ref_to); first by auto.
    iIntros (rankP) "HrankP".

    (*@     rankl, ok := rp.lowestRank(ts)                                      @*)
    (*@     if ok {                                                             @*)
    (*@         rank = rankl + 1                                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iRename "Hsafebk" into "Hsafebk'".
    do 2 iNamed "Hrp".
    wp_apply (wp_Replica__lowestRank with "Hpsmrkm").
    iIntros (rankl ok) "[Hpsmrkm %Hrankl]".
    wp_pures.

    (* FIXME: merge the two branches to reduce repeated proof. *)
    iNamed "Hgidrid".
    destruct ok; wp_pures.
    { wp_apply (wp_SumAssumeNoOverflow).
      iIntros "%Hnof".
      wp_store.
      iAssert (⌜(0 < uint.nat rankl)%nat⌝)%I as %Hnz.
      { iNamed "Hpsmrkm".
        specialize (Hvrank _ _ Hrankl). simpl in Hvrank.
        iPureIntro. apply Hvrank.
      }

      (*@     rp.advance(ts, rank)                                                @*)
      (*@                                                                         @*)
      wp_load.
      wp_apply (wp_Replica__advance with "Hpsmrkm").
      { clear -Hnof. word. }
      iIntros "Hpsmrkm".
      rewrite uint_nat_word_add_S; last first.
      { clear -Hnof. word. }

      (*@     logAdvance(rp.fname, rp.lsna, ts, rank)                             @*)
      (*@                                                                         @*)
      wp_load.
      iNamed "Hfname". iNamed "Hlsna".
      do 2 wp_loadField.
      wp_apply wp_logAdvance.
      (* Open the crash, replica, and file invariants. *)
      iMod (own_crash_ex_open with "Hdurable") as "[> Hdurable HdurableC]".
      { solve_ndisj. }
      iNamed "Hdurable".
      iNamed "Hinv".
      iInv "Hinv" as "> HinvO" "HinvC".
      iInv "Hinvfile" as "> HinvfileO" "HinvfileC".
      iNamed "HinvfileO".
      (* Agree on the fname, and merge the two ilog quarter. *)
      iDestruct (replica_ilog_fname_agree with "Hfname Hilogfname") as %->.
      iDestruct (replica_ilog_combine with "Hilog Hilogfileinv") as "[Hilog ->]".
      iApply ncfupd_mask_intro; first solve_ndisj.
      iIntros "Hmask".
      (* Give the file points-to to the logging method. *)
      iFrame "Hfile %".
      iIntros (bs' failed) "Hfile".
      destruct failed.
      { (* Case: Write failed. Close the invariants without any updates. *)
        iMod "Hmask" as "_".
        iDestruct (replica_ilog_split with "Hilog") as "[Hilog Hilogfileinv]".
        iMod ("HinvfileC" with "[Hfile Hilogfileinv]") as "_".
        { by iFrame "∗ # %". }
        iMod ("HinvC" with "HinvO") as "_".
        set dst := ReplicaDurable clog ilog.
        iMod ("HdurableC" $! dst with "[$Hclog $Hilog]") as "Hdurable".
        by iIntros "!> %Hcontra".
      }
      (* Case: Write succeeded. Update the logical state and re-establish invariant. *)
      iDestruct "Hfile" as "[Hfile %Hencilog']".
      iNamed "HinvO".
      iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
      iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]"; first apply Hgid.
      iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]"; first apply Hrid.
      (* First catching up the consistent log. *)
      destruct Hcloga as [cmdsa ->].
      iMod (replica_inv_execute with "Hclogalb Hclog Hilog Hgroup Hrp")
        as "(Hclog & Hilog & Hgroup & Hrp)".
      (* Then apply the validate transition. *)
      (* ∅ is a placeholder for participant groups. *)
      iMod (replica_inv_advance ts (S (uint.nat rankl)) (gid, rid) with "Hclog Hilog Hrp")
        as "(Hclog & Hilog & Hrp & H)".
      { apply Hexec. }
      { rewrite /advance_requirement Hrankl. clear. word. }
      iDestruct "H" as "(Htokens & #Hvote & %ra & %pa & #Hpromise & %Hlastacp)".
      (* Close the file, replica, and crash invariants. *)
      iDestruct (replica_ilog_split with "Hilog") as "[Hilog Hilogfileinv]".
      iMod "Hmask" as "_".
      iMod ("HinvfileC" with "[Hfile Hilogfileinv]") as "_".
      { iFrame "∗ #".
        iPureIntro.
        split.
        { apply Forall_app_2; first apply Hvilog.
          rewrite Forall_singleton.
          simpl.
          split.
          { clear -Hlencloga HlsnaW. word. }
          split; word.
        }
        { rewrite Hlencloga -HlsnaW.
          rewrite uint_nat_word_add_S in Hencilog'; last word.
          done.
        }
      }
      iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
      iDestruct ("HrgC" with "Hrp") as "Hrg".
      iDestruct ("HrgsC" with "Hrg") as "Hrgs".
      iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
      set ilog' := ilog ++ _.
      set dst := ReplicaDurable (clog ++ cmdsa) ilog'.
      iMod ("HdurableC" $! dst with "[$Hclog $Hilog]") as "Hdurable".
      iIntros "!> _".

      (*@     cid := tulip.CoordID{ GroupID: rp.gid, ReplicaID: rp.rid }          @*)
      (*@     btcoord := backup.Start(ts, rank, cid, ptgs, rp.gaddrm, 0, rp.proph) @*)
      (*@                                                                         @*)
      wp_pures.
      do 2 wp_loadField.
      wp_pures.
      iNamed "Hgaddrm". iNamed "Hproph".
      do 2 wp_loadField.
      wp_load.
      wp_apply (wp_Start _ _ (gid, rid) with
                 "Hlnrzed Hsafebk' Hptgs HgaddrmP Hgaddrm Hinv Hinvnets [Htokens]").
      { (* rank > 1 *) clear -Hnof Hnz. word. }
      { apply Hdomgaddrm. }
      { apply Hdomaddrm. }
      { by rewrite uint_nat_word_add_S; last word. }
      iIntros (tcoord) "Htcoord".
      wp_pures.

      (*@     go func() {                                                         @*)
      (*@         btcoord.Finalize()                                              @*)
      (*@     }()                                                                 @*)
      (*@ }                                                                       @*)
      wp_apply (wp_fork with "[Htcoord]").
      { (* Forked thread. *)
        iNext.
        wp_apply (wp_BackupTxnCoordinator__Finalize with "Htcoord").
        by iIntros "Htcoord".
      }
      wp_pures.
      iAssert ([∗ map] t ↦ ps ∈ init_psm ts psm, fast_proposal_witness γ gid rid t ps)%I
        as "#Hfpw'".
      { rewrite /init_psm.
        destruct (psm !! ts) as [ps |] eqn:Hps; first done.
        iApply big_sepM_insert_2; last done.
        rewrite /fast_proposal_witness /=.
        iNamed "Hpromise".
        iFrame "Hlb".
        iPureIntro.
        rewrite /last_accepted_decision Hps in Hlastacp.
        by destruct Hlastacp as [-> ->].
      }
      iApply "HΦ".
      iModIntro.
      iFrame "∗ # %".
      iPureIntro.
      split.
      { rewrite /init_psm.
        destruct (psm !! uint.nat tsW) as [p' |] eqn:Hpsmts.
        { apply elem_of_dom_2 in Hpsmts.
          rewrite dom_insert_L.
          clear -Hpsmts Hdompsmrkm.
          set_solver.
        }
        { rewrite 2!dom_insert_L.
          clear -Hdompsmrkm.
          set_solver.
        }
      }
      split; first done.
      rewrite merge_clog_ilog_snoc_ilog; last done.
      split.
      { rewrite Forall_forall.
        intros [n c] Hilog. simpl.
        apply elem_of_app in Hilog as [Hilog | Hnewc].
        { rewrite Forall_forall in Hvicmds. by specialize (Hvicmds _ Hilog). }
        rewrite list_elem_of_singleton in Hnewc.
        by inv Hnewc.
      }
      { by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=. }
    }
    { (*@     rp.advance(ts, rank)                                                @*)
      (*@                                                                         @*)
      wp_load.
      wp_apply (wp_Replica__advance with "Hpsmrkm").
      { clear. word. }
      iIntros "Hpsmrkm".

      (*@     logAdvance(rp.fname, rp.lsna, ts, rank)                             @*)
      (*@                                                                         @*)
      wp_load.
      iNamed "Hfname". iNamed "Hlsna".
      do 2 wp_loadField.
      wp_apply wp_logAdvance.
      (* Open the crash, replica, and file invariants. *)
      iMod (own_crash_ex_open with "Hdurable") as "[> Hdurable HdurableC]".
      { solve_ndisj. }
      iNamed "Hdurable".
      iNamed "Hinv".
      iInv "Hinv" as "> HinvO" "HinvC".
      iInv "Hinvfile" as "> HinvfileO" "HinvfileC".
      iNamed "HinvfileO".
      (* Agree on the fname, and merge the two ilog quarter. *)
      iDestruct (replica_ilog_fname_agree with "Hfname Hilogfname") as %->.
      iDestruct (replica_ilog_combine with "Hilog Hilogfileinv") as "[Hilog ->]".
      iApply ncfupd_mask_intro; first solve_ndisj.
      iIntros "Hmask".
      (* Give the file points-to to the logging method. *)
      iFrame "Hfile %".
      iIntros (bs' failed) "Hfile".
      destruct failed.
      { (* Case: Write failed. Close the invariants without any updates. *)
        iMod "Hmask" as "_".
        iDestruct (replica_ilog_split with "Hilog") as "[Hilog Hilogfileinv]".
        iMod ("HinvfileC" with "[Hfile Hilogfileinv]") as "_".
        { by iFrame "∗ # %". }
        iMod ("HinvC" with "HinvO") as "_".
        set dst := ReplicaDurable clog ilog.
        iMod ("HdurableC" $! dst with "[$Hclog $Hilog]") as "Hdurable".
        by iIntros "!> %Hcontra".
      }
      (* Case: Write succeeded. Update the logical state and re-establish invariant. *)
      iDestruct "Hfile" as "[Hfile %Hencilog']".
      iNamed "HinvO".
      iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
      iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]"; first apply Hgid.
      iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]"; first apply Hrid.
      (* First catching up the consistent log. *)
      destruct Hcloga as [cmdsa ->].
      iMod (replica_inv_execute with "Hclogalb Hclog Hilog Hgroup Hrp")
        as "(Hclog & Hilog & Hgroup & Hrp)".
      (* Then apply the validate transition. *)
      (* ∅ is a placeholder for participant groups. *)
      iMod (replica_inv_advance ts 2%nat (gid, rid) with "Hclog Hilog Hrp")
        as "(Hclog & Hilog & Hrp & H)".
      { apply Hexec. }
      { rewrite /advance_requirement Hrankl. clear. word. }
      iDestruct "H" as "(Htokens & #Hvote & %ra & %pa & #Hpromise & %Hlastacp)".
      (* Close the file, replica, and crash invariants. *)
      iDestruct (replica_ilog_split with "Hilog") as "[Hilog Hilogfileinv]".
      iMod "Hmask" as "_".
      iMod ("HinvfileC" with "[Hfile Hilogfileinv]") as "_".
      { iFrame "∗ #".
        iPureIntro.
        split.
        { apply Forall_app_2; first apply Hvilog.
          rewrite Forall_singleton.
          simpl.
          split.
          { clear -Hlencloga HlsnaW. word. }
          split; word.
        }
        { by rewrite Hlencloga -HlsnaW. }
      }
      iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
      iDestruct ("HrgC" with "Hrp") as "Hrg".
      iDestruct ("HrgsC" with "Hrg") as "Hrgs".
      iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
      set ilog' := ilog ++ _.
      set dst := ReplicaDurable (clog ++ cmdsa) ilog'.
      iMod ("HdurableC" $! dst with "[$Hclog $Hilog]") as "Hdurable".
      iIntros "!> _".

      (*@     cid := tulip.CoordID{ GroupID: rp.gid, ReplicaID: rp.rid }          @*)
      (*@     btcoord := backup.Start(ts, rank, cid, ptgs, rp.gaddrm, 0, rp.proph) @*)
      (*@                                                                         @*)
      wp_pures.
      do 2 wp_loadField.
      wp_pures.
      iNamed "Hgaddrm". iNamed "Hproph".
      do 2 wp_loadField.
      wp_load.
      wp_apply (wp_Start _ _ (gid, rid)
                 with "Hlnrzed Hsafebk' Hptgs HgaddrmP Hgaddrm Hinv Hinvnets [Htokens]").
      { (* rank > 1 *) word. }
      { apply Hdomgaddrm. }
      { apply Hdomaddrm. }
      { simpl. by replace (uint.nat (W64 2)) with 2%nat by word. }
      iIntros (tcoord) "Htcoord".
      wp_pures.

      (*@     go func() {                                                         @*)
      (*@         btcoord.Finalize()                                              @*)
      (*@     }()                                                                 @*)
      (*@ }                                                                       @*)
      wp_apply (wp_fork with "[Htcoord]").
      { (* Forked thread. *)
        iNext.
        wp_apply (wp_BackupTxnCoordinator__Finalize with "Htcoord").
        by iIntros "Htcoord".
      }
      wp_pures.
      iAssert ([∗ map] t ↦ ps ∈ init_psm ts psm, fast_proposal_witness γ gid rid t ps)%I
        as "#Hfpw'".
      { rewrite /init_psm.
        destruct (psm !! ts) as [ps |] eqn:Hps; first done.
        iApply big_sepM_insert_2; last done.
        rewrite /fast_proposal_witness /=.
        iNamed "Hpromise".
        iFrame "Hlb".
        iPureIntro.
        rewrite /last_accepted_decision Hps in Hlastacp.
        by destruct Hlastacp as [-> ->].
      }
      iApply "HΦ".
      iModIntro.
      iFrame "∗ # %".
      iPureIntro.
      split.
      { rewrite /init_psm.
        destruct (psm !! uint.nat tsW) as [p' |] eqn:Hpsmts.
        { apply elem_of_dom_2 in Hpsmts.
          rewrite dom_insert_L.
          clear -Hpsmts Hdompsmrkm.
          set_solver.
        }
        { rewrite 2!dom_insert_L.
          clear -Hdompsmrkm.
          set_solver.
        }
      }
      split; first done.
      rewrite merge_clog_ilog_snoc_ilog; last done.
      split.
      { rewrite Forall_forall.
        intros [n c] Hilog. simpl.
        apply elem_of_app in Hilog as [Hilog | Hnewc].
        { rewrite Forall_forall in Hvicmds. by specialize (Hvicmds _ Hilog). }
        rewrite list_elem_of_singleton in Hnewc.
        by inv Hnewc.
      }
      { by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=. }
    }
  Qed.

End program.
