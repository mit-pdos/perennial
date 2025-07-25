From Perennial.program_proof.tulip.invariance Require Import execute validate accept.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_finalized replica_last_proposal replica_try_acquire
  replica_accept replica_memorize replica_refresh replica_log.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__fastPrepare
    rp (tsW : u64) pwrsS pwrs ptgsS ptgs gid rid γ α :
    let ts := uint.nat tsW in
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    is_lnrz_tid γ ts -∗
    safe_txn_pwrs γ gid ts pwrs -∗
    safe_txn_ptgs γ ts ptgs -∗
    is_dbmap_in_slice pwrsS pwrs -∗
    is_txnptgs_in_slice ptgsS ptgs -∗
    know_tulip_inv γ -∗
    know_replica_file_inv γ gid rid -∗
    {{{ own_replica rp gid rid γ α }}}
      Replica__fastPrepare #rp #tsW (to_val pwrsS) (to_val ptgsS)
    {{{ (res : rpres), RET #(rpres_to_u64 res);
        own_replica rp gid rid γ α ∗ fast_prepare_outcome γ gid rid ts res
    }}}.
  Proof.
    iIntros (ts Hgid Hrid) "#Hlnrz #Hsafepwrs #Hsafeptgs #Hpwrs #Hptgs #Hinv #Hinvfile".
    iIntros (Φ) "!> Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) fastPrepare(ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) uint64 { @*)
    (*@     // Check if the transaction has aborted or committed. If so, returns the @*)
    (*@     // status immediately.                                              @*)
    (*@     res, final := rp.finalized(ts)                                      @*)
    (*@     if final {                                                          @*)
    (*@         return res                                                      @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__finalized with "Hinv Hrp").
    { apply Hgid. }
    iIntros (res final) "[Hrp Hfinal]".
    wp_pures.
    destruct final; wp_pures.
    { iApply ("HΦ" $! res). iFrame "Hrp". by destruct res. }

    (*@     // Check if the coordinator is the most recent one. If not, report the @*)
    (*@     // existence of a more recent coordinator.                          @*)
    (*@     rank, dec, ok := rp.lastProposal(ts)                                @*)
    (*@     if ok {                                                             @*)
    (*@         if 0 < rank {                                                   @*)
    (*@             // TODO: This would be a performance problem if @pp.rank = 1 (i.e., @*)
    (*@             // txn client's slow-path prepare) since the client would stops its @*)
    (*@             // 2PC on receiving such response. For now the ad-hoc fix is to not @*)
    (*@             // respond to the client in this case, but should figure out a more @*)
    (*@             // efficient design.                                        @*)
    (*@             return tulip.REPLICA_STALE_COORDINATOR                      @*)
    (*@         }                                                               @*)
    (*@         if !dec {                                                       @*)
    (*@             return tulip.REPLICA_FAILED_VALIDATION                      @*)
    (*@         }                                                               @*)
    (*@         return tulip.REPLICA_OK                                         @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hrp".
    wp_apply (wp_Replica__lastProposal with "Hpsmrkm").
    iIntros (rank dec ok) "[Hpsmrkm %Hok]".
    wp_pures.
    destruct ok; wp_pures.
    { case_bool_decide as Hrank; wp_pures.
      { iApply ("HΦ" $! ReplicaStaleCoordinator). by iFrame "∗ # %". }
      destruct dec; wp_pures; last first.
      { iApply ("HΦ" $! ReplicaFailedValidation).
        iDestruct (big_sepM_lookup with "Hfpw") as "#Hnp".
        { apply Hok. }
        rewrite /fast_proposal_witness.
        assert (Hz : uint.nat rank = O) by word.
        case_decide as Hfast; simpl in Hfast; last word.
        iDestruct "Hnp" as "[Hnp _]".
        by iFrame "∗ # %".
      }
      { iApply ("HΦ" $! ReplicaOK).
        iDestruct (big_sepM_lookup with "Hfpw") as "#Hpv".
        { apply Hok. }
        rewrite /fast_proposal_witness.
        assert (Hz : uint.nat rank = O) by word.
        case_decide as Hfast; simpl in Hfast; last word.
        simpl.
        iDestruct "Hpv" as "[Hprepared Hvalidated]".
        by iFrame "∗ # %".
      }
    }

    (*@     // If the replica has validated this transaction, but no corresponding @*)
    (*@     // prepare proposal entry (as is the case after passing the conditional @*)
    (*@     // above), this means the client has already proceeded to the slow path, and @*)
    (*@     // hence there's nothing more to be done with this fast-prepare.    @*)
    (*@     _, validated := rp.prepm[ts]                                        @*)
    (*@     if validated {                                                      @*)
    (*@         return tulip.REPLICA_STALE_COORDINATOR                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hcpm". wp_loadField.
    wp_apply (wp_MapGet with "HprepmS").
    iIntros (prepS validated) "[%Hvalidated HprepmS]".
    wp_pures.
    destruct validated; wp_pures.
    { iApply ("HΦ" $! ReplicaStaleCoordinator). by iFrame "∗ # %". }

    (*@     // Validate timestamps.                                             @*)
    (*@     acquired := rp.tryAcquire(ts, pwrs)                                 @*)
    (*@                                                                         @*)
    iDestruct (safe_txn_pwrs_dom_pwrs with "Hsafepwrs") as %Hdompwrs.
    wp_apply (wp_Replica__tryAcquire with "Hpwrs Hptsmsptsm").
    { apply Hdompwrs. }
    iIntros (acquired) "Hptsmsptsm".

    (*@     // Update prepare status table to record that @ts is prepared or unprepared @*)
    (*@     // at rank 0.                                                       @*)
    (*@     rp.accept(ts, 0, acquired)                                          @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__accept with "Hpsmrkm").
    iIntros "Hpsmrkm".

    (*@     if !acquired {                                                      @*)
    (*@         // Logical actions: Execute() and then Accept(@ts, @0, @false). @*)
    (*@         rp.logAccept(ts, 0, false)                                      @*)
    (*@         return tulip.REPLICA_FAILED_VALIDATION                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_pures.
    destruct acquired; wp_pures; last first.
    { wp_pures.
      iNamed "Hlsna".
      wp_loadField.
      iNamed "Hfname".
      wp_loadField.
      wp_apply wp_logAccept.
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
      (* Then snoc the new inconsistent command. *)
      iMod (replica_inv_accept ts O false with "[] Hclog Hilog Hrp")
        as "(Hclog & Hilog & Hrp & #Hacc)".
      { apply Hexec. }
      { rewrite /accept_requirement.
        destruct (rkm !! ts) as [r |] eqn:Hr; last done.
        apply elem_of_dom_2 in Hr.
        rewrite -not_elem_of_dom Hdompsmrkm in Hok.
        by destruct Hok as [Hnotin _].
      }
      { done. }
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
          split; [word | done].
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
      wp_pures.
      iApply ("HΦ" $! ReplicaFailedValidation).
      iFrame "∗ # %".
      iModIntro.
      iSplit.
      { iApply (big_sepM_insert_2 with "[] Hfpw").
        rewrite /fast_proposal_witness /=.
        case_decide; last done.
        iFrame "Hacc".
      }
      iPureIntro.
      split.
      { by rewrite 2!dom_insert_L Hdompsmrkm. }
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
    iDestruct "Hptsmsptsm" as "(Hptsmsptsm & %Hvptsm & %Hvsptsm)".

    (* Normally we log at the end to save one [iApply ncfupd_wp], but
    since @rp.memorize consumes the ownership of [Hpwrs], we log one step
    earlier. *)

    (*@     // Logical actions: Execute() and then Validate(@ts, @pwrs, @ptgs) and @*)
    (*@     // Accept(@ts, @0, @true).                                          @*)
    (*@     logFastPrepare(rp.fname, rp.lsna, ts, pwrs, ptgs)                   @*)
    (*@                                                                         @*)
    wp_pures.
    iNamed "Hlsna".
    wp_loadField.
    iNamed "Hfname".
    wp_loadField.
    wp_apply (wp_logFastPrepare with "Hpwrs Hptgs").
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
    iDestruct (big_sepM2_dom with "Hprepm") as %Hdomprepm.
    iMod (replica_inv_validate with "Hlnrz Hsafepwrs Hsafeptgs Hclog Hilog Hrp")
      as "(Hclog & Hilog & Hrp & #Hvd)".
    { apply Hexec. }
    { do 2 (split; first done).
      apply map_get_false in Hvalidated as [Hnone _].
      symmetry in Hcpmabs.
      rewrite -not_elem_of_dom Hdomprepm not_elem_of_dom in Hnone.
      unshelve epose proof (lookup_kmap_eq_None _ _ _ _ _ Hcpmabs Hnone) as Hcpm.
      apply Hcpm.
      word.
    }
    iDestruct (replica_inv_weaken with "Hrp") as "Hrp".
    iMod (replica_inv_accept ts O true with "[] Hclog Hilog Hrp")
      as "(Hclog & Hilog & Hrp & #Hacc)".
    { rewrite merge_clog_ilog_snoc_ilog; last done.
      by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=.
    }
    { rewrite /accept_requirement.
      destruct (rkm !! ts) as [r |] eqn:Hr; last done.
      apply elem_of_dom_2 in Hr.
      rewrite -not_elem_of_dom Hdompsmrkm in Hok.
      by destruct Hok as [Hnotin _].
    }
    { iFrame "Hvd". }
    (* Close the file, replica, and crash invariants. *)
    iDestruct (replica_ilog_split with "Hilog") as "[Hilog Hilogfileinv]".
    iMod "Hmask" as "_".
    rewrite -app_assoc.
    iMod ("HinvfileC" with "[Hfile Hilogfileinv]") as "_".
    { iFrame "∗ #".
      iPureIntro.
      split.
      { apply Forall_app_2; first apply Hvilog.
        apply Forall_cons_2.
        { simpl.
          split.
          { clear -Hlencloga HlsnaW. word. }
          split; [word | done].
        }
        rewrite Forall_singleton /=.
        split.
        { clear -Hlencloga HlsnaW. word. }
        split; [word | done].
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

    (*@     // Record the write set and the participant groups.                 @*)
    (*@     rp.memorize(ts, pwrs, ptgs)                                         @*)
    (*@                                                                         @*)
    iAssert (own_replica_cpm rp cpm)%I with "[$HprepmP $HprepmS $Hprepm]" as "Hcpm".
    { done. }
    wp_apply (wp_Replica__memorize with "Hpwrs Hptgs [$Hcpm $Hpgm]").
    iIntros "[Hcpm Hpgm]".

    (*@     return tulip.REPLICA_OK                                             @*)
    (*@ }                                                                       @*)
    wp_pures.
    iApply ("HΦ" $! ReplicaOK).
    iAssert ([∗ set] t ∈ dom (<[ts := pwrs]> cpm), is_replica_validated_ts γ gid rid t)%I
      as "Hrpvds'".
    { rewrite dom_insert_L.
      iApply (big_sepS_insert_2 ts with "Hvd Hrpvds").
    }
    iClear "Hrpvds".
    iAssert ([∗ map] t ↦ ps ∈ <[ts := (O, true)]> psm, fast_proposal_witness γ gid rid t ps)%I
      as "Hfpw'".
    { iApply (big_sepM_insert_2 with "[] Hfpw").
      rewrite /fast_proposal_witness /=.
      iFrame "Hvd Hacc".
    }
    iClear "Hfpw".
    iDestruct (safe_txn_pwrs_impl_valid_wrs with "Hsafepwrs") as %Hvw.
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { by iApply big_sepM_insert_2. }
    iSplit.
    { rewrite !dom_insert_L. by iApply big_sepS_insert_2. }
    iSplit.
    { iApply big_sepM_insert_2; last done.
      iApply (safe_txn_pwrs_ptgs_backup_txn with "Hsafepwrs Hsafeptgs").
    }
    iPureIntro.
    split.
    { by rewrite 2!dom_insert_L Hdompsmrkm. }
    split; first done.
    subst ilog'.
    rewrite app_assoc.
    do 2 (rewrite merge_clog_ilog_snoc_ilog; last done).
    rewrite /execute_cmds foldl_snoc execute_cmds_unfold.
    split.
    { by apply map_Forall_insert_2. }
    split.
    { rewrite Forall_forall.
      intros [n c] Hilog. simpl.
      apply elem_of_app in Hilog as [Hilog | Hnewc].
      { apply elem_of_app in Hilog as [Hilog | Hnewc].
        { rewrite Forall_forall in Hvicmds. by specialize (Hvicmds _ Hilog). }
        rewrite list_elem_of_singleton in Hnewc.
        by inv Hnewc.
      }
      rewrite list_elem_of_singleton in Hnewc.
      by inv Hnewc.
    }
    { by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=. }
  Qed.

  Theorem wp_Replica__FastPrepare
    rp (tsW : u64) pwrsS pwrs ptgsS ptgs gid rid γ :
    let ts := uint.nat tsW in
    is_lnrz_tid γ ts -∗
    safe_txn_pwrs γ gid ts pwrs -∗
    safe_txn_ptgs γ ts ptgs -∗
    is_dbmap_in_slice pwrsS pwrs -∗
    is_txnptgs_in_slice ptgsS ptgs -∗
    is_replica rp gid rid γ -∗
    {{{ True }}}
      Replica__FastPrepare #rp #tsW (to_val pwrsS) (to_val ptgsS)
    {{{ (res : rpres), RET #(rpres_to_u64 res);
        fast_prepare_outcome γ gid rid ts res
    }}}.
  Proof.
    iIntros (ts) "#Hlnrz #Hsafepwrs #Hsafeptgs #Hpwrs #Hptgs #Hrp".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) FastPrepare(ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) uint64 { @*)
    (*@     rp.mu.Lock()                                                        @*)
    (*@     res := rp.fastPrepare(ts, pwrs, ptgs)                               @*)
    (*@     rp.refresh(ts, 0)                                                   @*)
    (*@     rp.mu.Unlock()                                                      @*)
    (*@     return res                                                          @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hrp]".
    iNamed "Hgidrid".
    wp_apply (wp_Replica__fastPrepare with "Hlnrz Hsafepwrs Hsafeptgs Hpwrs Hptgs [$Hinv] Hinvfile Hrp").
    { apply Hgid. }
    { apply Hrid. }
    iIntros (res) "[Hrp #Hfp]".
    wp_apply (wp_Replica__refresh with "Hrp").
    iIntros "Hrp".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hrp]").
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
