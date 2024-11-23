From Perennial.program_proof.tulip.invariance Require Import execute validate accept.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_finalized replica_last_proposal replica_acquire
  replica_accept replica_log.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__fastPrepare
    rp (tsW : u64) pwrsS pwrsL pwrs (ptgsS : Slice.t) gid rid γ α :
    let ts := uint.nat tsW in
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    safe_txn_pwrs γ gid ts pwrs -∗
    know_tulip_inv γ -∗
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs ∗ own_replica rp gid rid γ α }}}
      Replica__fastPrepare #rp #tsW (to_val pwrsS) (to_val ptgsS)
    {{{ (res : rpres), RET #(rpres_to_u64 res);
        own_replica rp gid rid γ α ∗ fast_prepare_outcome γ gid rid ts res
    }}}.
  Proof.
    iIntros (ts Hgid Hrid) "#Hsafepwrs #Hinv".
    iIntros (Φ) "!> [Hpwrs Hrp] HΦ".
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
    (*@     acquired := rp.acquire(ts, pwrs)                                    @*)
    (*@                                                                         @*)
    iDestruct (safe_txn_pwrs_dom_pwrs with "Hsafepwrs") as %Hdompwrs.
    wp_apply (wp_Replica__acquire with "[$Hpwrs $Hptsmsptsm]").
    { apply Hdompwrs. }
    iIntros (acquired) "[Hpwrs Hptsmsptsm]".

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
    { wp_apply wp_Replica__logAccept.
      wp_pures.
      iInv "Hinv" as "> HinvO" "HinvC".
      iNamed "HinvO".
      iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
      iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]"; first apply Hgid.
      iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]"; first apply Hrid.
      (* First catching up the consistent log. *)
      destruct Hcloga as [cmdsa ->].
      iMod (replica_inv_execute with "Hclogalb Hclog Hilog Hgroup Hrp")
        as "(Hclog & Hilog & Hgroup & Hrp)".
      iMod (replica_inv_accept ts O false with "[] Hclog Hilog Hrp")
        as "(Hclog & Hilog & Hrp & #Hacc)".
      { apply Hexec. }
      { rewrite /accept_requirement.
        destruct (rkm !! ts) as [r |] eqn:Hr; last done.
        apply elem_of_dom_2 in Hr.
        by rewrite -not_elem_of_dom Hdompsmrkm in Hok.
      }
      { done. }
      iDestruct ("HrgC" with "Hrp") as "Hrg".
      iDestruct ("HrgsC" with "Hrg") as "Hrgs".
      iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
      iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
      iApply ("HΦ" $! ReplicaFailedValidation).
      iFrame "∗ # %".
      iModIntro.
      iExists ptgsm.
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
        rewrite elem_of_list_singleton in Hnewc.
        by inv Hnewc.
      }
      { by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=. }
    }
    iDestruct "Hptsmsptsm" as "(Hptsmsptsm & %Hvptsm & %Hvsptsm)".

    (*@     // Record the write set and the participant groups.                 @*)
    (*@     rp.prepm[ts] = pwrs                                                 @*)
    (*@     // rp.ptgsm[ts] = ptgs                                              @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_MapInsert with "HprepmS"); first done.
    iIntros "HprepmS".

    (*@     // Logical actions: Execute() and then Validate(@ts, @pwrs, @ptgs) and @*)
    (*@     // Accept(@ts, @0, @true).                                          @*)
    (*@     rp.logFastPrepare(ts, pwrs, ptgs)                                   @*)
    (*@                                                                         @*)
    wp_apply wp_Replica__logFastPrepare.
    wp_pures.
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]"; first apply Hrid.
    (* First catching up the consistent log. *)
    destruct Hcloga as [cmdsa ->].
    iMod (replica_inv_execute with "Hclogalb Hclog Hilog Hgroup Hrp")
      as "(Hclog & Hilog & Hgroup & Hrp)".
    iDestruct (big_sepM2_dom with "Hprepm") as %Hdomprepm.
    iMod (replica_inv_validate _ _ ∅ with "Hsafepwrs Hclog Hilog Hrp")
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
    iMod (replica_inv_accept ts O true with "[] Hclog Hilog Hrp")
      as "(Hclog & Hilog & Hrp & #Hacc)".
    { rewrite merge_clog_ilog_snoc_ilog; last done.
      by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=.
    }
    { rewrite /accept_requirement.
      destruct (rkm !! ts) as [r |] eqn:Hr; last done.
      apply elem_of_dom_2 in Hr.
      by rewrite -not_elem_of_dom Hdompsmrkm in Hok.
    }
    { iFrame "Hvd". }
    iDestruct ("HrgC" with "Hrp") as "Hrg".
    iDestruct ("HrgsC" with "Hrg") as "Hrgs".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".

    (*@     return tulip.REPLICA_OK                                             @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! ReplicaOK).
    iDestruct (big_sepM2_insert_2 _ _ _ tsW with "[Hpwrs] Hprepm") as "Hprepm".
    { iFrame "Hpwrs". }
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
    iPureIntro. simpl.
    exists (<[ts := ∅]> ptgsm).
    split.
    { rewrite 2!kmap_insert. f_equal; [word | done]. }
    split.
    { by rewrite 2!dom_insert_L Hdompsmrkm. }
    split; first done.
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
        rewrite elem_of_list_singleton in Hnewc.
        by inv Hnewc.
      }
      rewrite elem_of_list_singleton in Hnewc.
      by inv Hnewc.
    }
    { by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=. }
  Qed.

End program.
