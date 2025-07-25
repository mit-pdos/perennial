From Perennial.program_proof.tulip.invariance Require Import execute advance.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_finalized replica_lowest_rank replica_validated
  replica_last_proposal replica_advance replica_log replica_refresh.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__inquire
    (rp : loc) (tsW : u64) (rankW : u64) (cid : coordid) gid rid γ α :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    valid_ts ts ->
    valid_backup_rank rank ->
    know_tulip_inv γ -∗
    know_replica_file_inv γ gid rid -∗
    {{{ own_replica rp gid rid γ α }}}
      Replica__inquire #rp #tsW #rankW
    {{{ (pp : ppsl) (vd : bool) (pwrsP : Slice.t) (res : rpres) (pwrs : dbmap),
          RET (ppsl_to_val pp, #vd, to_val pwrsP, #(rpres_to_u64 res)); 
        own_replica rp gid rid γ α ∗
        inquire_outcome γ gid rid cid ts rank (uint.nat pp.1) pp.2 vd pwrs res ∗
        if vd then is_dbmap_in_slice pwrsP pwrs else True
    }}}.
  Proof.
    iIntros (ts rank Hgid Hrid Hvts Hvrank) "#Hinv #Hinvfile".
    iIntros (Φ) "!> Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) inquire(ts uint64, rank uint64) (tulip.PrepareProposal, bool, []tulip.WriteEntry, uint64) { @*)
    (*@     // Check if the transaction has aborted or committed. If so, returns the @*)
    (*@     // status immediately.                                              @*)
    (*@     res, done := rp.finalized(ts)                                       @*)
    (*@     if done {                                                           @*)
    (*@         return tulip.PrepareProposal{}, false, nil, res                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_pures.
    wp_apply (wp_Replica__finalized with "Hinv Hrp").
    { apply Hgid. }
    iIntros (res final) "[Hrp Hres]".
    wp_pures.
    destruct final; wp_pures.
    { iModIntro.
      iApply ("HΦ" $! (W64 0, false) false Slice.nil res ∅).
      iFrame "Hrp".
      iSplit; last done.
      by destruct res.
    }

    (*@     // Check if @rank is still available. Note the difference between this @*)
    (*@     // method and @tryAccept: The case where @rank = @ps.rankl indicates another @*)
    (*@     // replica's attempt to become the coordinator at @rank, which should be @*)
    (*@     // rejected. Note the rank setup: rank 0 and 1 are reserved for the client @*)
    (*@     // (similarly to Paxos's ballot assignment), and the others are contended by @*)
    (*@     // replicas (similarly to Raft's voting process).                   @*)
    (*@     rankl, ok := rp.lowestRank(ts)                                      @*)
    (*@     if ok && rank <= rankl {                                            @*)
    (*@         return tulip.PrepareProposal{}, false, nil, tulip.REPLICA_STALE_COORDINATOR @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hrp".
    wp_apply (wp_Replica__lowestRank with "Hpsmrkm").
    iIntros (rankl ok) "[Hpsmrkm %Hrankl]".
    wp_pures.
    unshelve wp_apply (wp_and_pure (ok = true)).
    { shelve. }
    { apply _. }
    { shelve. }
    { wp_pures. case_bool_decide as Hcase; last apply not_true_is_false in Hcase; by subst ok. }
    { iIntros (_). by wp_pures. }
    case_bool_decide as Hadvanced; wp_pures.
    { iApply ("HΦ" $! (W64 0, false) false Slice.nil ReplicaStaleCoordinator ∅).
      by iFrame "∗ # %".
    }

    (*@     // Note that in the case where the fast path is not taken (i.e., @ok = @*)
    (*@     // false), we want (0, false), which happens to be the zero-value.  @*)
    (*@     ranka, pdec, _ := rp.lastProposal(ts)                               @*)
    (*@     pp := tulip.PrepareProposal{ Rank: ranka, Prepared: pdec }          @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__lastProposal with "Hpsmrkm").
    iIntros (ranka pdec ex) "[Hpsmrkm %Hex]".

    (*@     // Update the lowest acceptable rank.                               @*)
    (*@     // Logical action: Advance lowest acceptable rank of @ts to @rank.  @*)
    (*@     rp.advance(ts, rank)                                                @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__advance with "Hpsmrkm").
    { rewrite /valid_backup_rank in Hvrank. clear -Hvrank. word. }
    iIntros "Hpsmrkm".

    (*@     // Create an inconsistent log entry.                                @*)
    (*@     logAdvance(rp.fname, rp.lsna, ts, rank)                             @*)
    (*@                                                                         @*)
    wp_pures.
    iNamed "Hlsna".
    wp_loadField.
    iNamed "Hfname".
    wp_loadField.
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
    iMod (replica_inv_advance ts rank cid with "Hclog Hilog Hrp")
      as "(Hclog & Hilog & Hrp & H)".
    { apply Hexec. }
    { rewrite /advance_requirement.
      destruct ok; rewrite Hrankl.
      { (* Case: Has heard from coordinator @rankl. *)
        rewrite not_and_r in Hadvanced.
        destruct Hadvanced as [? | Horder]; first done.
        clear -Horder. word.
      }
      { (* Case: Has not heard from any coordinator. *)
        clear -Hvrank. rewrite /valid_backup_rank in Hvrank. lia.
      }
    }
    iDestruct "H" as "(_ & #Hvote & %ra & %pa & #Hpromise & %Hlastacp)".
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
        split.
        { rewrite /valid_ts in Hvts. clear -Hvts. word. }
        { rewrite /valid_backup_rank in Hvrank. clear -Hvrank. word. }
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

    (*@     // Check whether the transaction has validated.                     @*)
    (*@     pwrs, vd := rp.prepm[ts]                                            @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__validated with "Hcpm").
    iIntros (pwrsP vd) "[Hcpm #Hpwrs]".
    wp_pures.

    (*@     // Return the last accepted prepare decision.                       @*)
    (*@     return pp, vd, pwrs, tulip.REPLICA_OK                               @*)
    (*@ }                                                                       @*)
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
    iClear "Hfpw".
    iAssert (own_replica rp gid rid γ α)%I with "[-HΦ]" as "Hrp".
    { iFrame "∗ # %".
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
    rewrite /last_accepted_decision in Hlastacp.
    iNamed "Hpromise".
    destruct vd eqn:Hvd; last first.
    { iModIntro.
      iApply ("HΦ" $! (ranka, pdec) _ _ ReplicaOK ∅). simpl.
      destruct ex.
      { rewrite Hex /= in Hlastacp.
        iFrame "Hrp".
        iSplit; last done.
        inv Hlastacp as [Heq].
        rewrite Heq in Hp *.
        iFrame "# %".
      }
      { destruct Hex as (Hpsmts & Hranka & Hpdec).
        rewrite Hpsmts in Hlastacp.
        iFrame "Hrp".
        iSplit; last done.
        inv Hlastacp as [Heq].
        rewrite Heq in Hp *.
        iFrame "# %".
      }
    }
    iDestruct "Hpwrs" as (pwrs) "[Hpwrs %Hpwrs]".
    iDestruct (big_sepS_elem_of with "Hrpvds") as "Hvd".
    { apply elem_of_dom_2 in Hpwrs. apply Hpwrs. }
    iDestruct (big_sepM_lookup with "Hsafetpwrs") as "Hsafepwrs".
    { apply Hpwrs. }
    iApply ("HΦ" $! (ranka, pdec) _ _ ReplicaOK pwrs). simpl.
    destruct ex.
    { rewrite Hex /= in Hlastacp.
      inv Hlastacp as [Heq].
      rewrite Heq in Hp *.
      by iFrame "∗ # %".
    }
    { destruct Hex as (Hpsmts & Hranka & Hpdec).
      rewrite Hpsmts in Hlastacp.
      inv Hlastacp as [Heq].
      rewrite Heq in Hp *.
      by iFrame "∗ # %".
    }
  Qed.

  Theorem wp_Replica__Inquire
    (rp : loc) (tsW : u64) (rankW : u64) (cid : coordid) gid rid γ :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    valid_ts ts ->
    valid_backup_rank rank ->
    is_replica rp gid rid γ -∗
    {{{ True }}}
      Replica__Inquire #rp #tsW #rankW
    {{{ (pp : ppsl) (vd : bool) (pwrsP : Slice.t) (res : rpres) (pwrs : dbmap),
          RET (ppsl_to_val pp, #vd, to_val pwrsP, #(rpres_to_u64 res)); 
        inquire_outcome γ gid rid cid ts rank (uint.nat pp.1) pp.2 vd pwrs res ∗
        if vd then is_dbmap_in_slice pwrsP pwrs else True
    }}}.
  Proof.
    iIntros (ts rank Hvts Hvrank) "#Hrp".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) Inquire(ts uint64, rank uint64) (tulip.PrepareProposal, bool, []tulip.WriteEntry, uint64) { @*)
    (*@     rp.mu.Lock()                                                        @*)
    (*@     pp, vd, pwrs, res := rp.inquire(ts, rank)                           @*)
    (*@     rp.refresh(ts, rank)                                                @*)
    (*@     rp.mu.Unlock()                                                      @*)
    (*@     return pp, vd, pwrs, res                                            @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hrp]".
    iNamed "Hgidrid".
    wp_apply (wp_Replica__inquire with "[$Hinv] Hinvfile Hrp").
    { apply Hgid. }
    { apply Hrid. }
    { apply Hvts. }
    { apply Hvrank. }
    iIntros (pp vd pwrsP res pwrs) "[Hrp [#Hinq #Hpwrs]]".
    wp_pures.
    wp_apply (wp_Replica__refresh with "Hrp").
    iIntros "Hrp".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hrp]").
    wp_pures.
    iApply "HΦ".
    by iFrame "#".
  Qed.

End program.
