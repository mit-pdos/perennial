From Perennial.program_proof.tulip.invariance Require Import execute accept.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_finalized replica_lowest_rank replica_accept replica_log.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__tryAccept rp (tsW : u64) (rankW : u64) (dec : bool) gid rid γ α :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    rank ≠ O ->
    is_group_prepare_proposal γ gid ts rank dec -∗
    know_tulip_inv γ -∗
    know_replica_file_inv γ gid rid -∗
    {{{ own_replica rp gid rid γ α }}}
      Replica__tryAccept #rp #tsW #rankW #dec
    {{{ (res : rpres), RET #(rpres_to_u64 res);
        own_replica rp gid rid γ α ∗ accept_outcome γ gid rid ts rank dec res
    }}}.
  Proof.
    iIntros (ts rank Hgid Hrid Hranknz) "#Hgpsl #Hinv #Hinvfile".
    iIntros (Φ) "!> Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) tryAccept(ts uint64, rank uint64, dec bool) uint64 { @*)
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
    (*@     rankl, ok := rp.lowestRank(ts)                                      @*)
    (*@     if ok && rank < rankl {                                             @*)
    (*@         return tulip.REPLICA_STALE_COORDINATOR                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hrp".
    wp_apply (wp_Replica__lowestRank with "Hpsmrkm").
    iIntros (rankl ok) "[Hpsmrkm %Hok]".
    wp_pures.
    unshelve wp_apply (wp_and_pure (ok = true)).
    { shelve. }
    { apply _. }
    { shelve. }
    { wp_pures. case_bool_decide as Hcase; last apply not_true_is_false in Hcase; by subst ok. }
    { iIntros (_). by wp_pures. }
    case_bool_decide as Hcase; wp_pures.
    { iApply ("HΦ" $! ReplicaStaleCoordinator). by iFrame "∗ # %". }

    (*@     // Update prepare status table to record that @ts is prepared at @rank. @*)
    (*@     rp.accept(ts, rank, dec)                                            @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__accept with "Hpsmrkm").
    iIntros "Hpsmrkm".
    wp_pures.

    (*@     // Logical actions: Execute() and then Accept(@ts, @rank, @dec).    @*)
    (*@     rp.logAccept(ts, rank, dec)                                         @*)
    (*@                                                                         @*)
    wp_pures.
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
    iMod (replica_inv_accept ts rank dec with "[Hgpsl] Hclog Hilog Hrp")
      as "(Hclog & Hilog & Hrp & #Hacc)".
    { apply Hexec. }
    { rewrite /accept_requirement.
      destruct ok; rewrite Hok; last done.
      apply Classical_Prop.not_and_or in Hcase.
      destruct Hcase as [? | Hge]; first done.
      clear -Hge. lia.
    }
    { case_decide as Hrank; [word | done]. }
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
        word.
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

    (*@     return tulip.REPLICA_OK                                             @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! ReplicaOK).
    iAssert ([∗ map] t ↦ ps ∈ <[ts := (rank, dec)]> psm, fast_proposal_witness γ gid rid t ps)%I
      as "Hfpw'".
    { iApply (big_sepM_insert_2 with "[] Hfpw").
      rewrite /fast_proposal_witness /=.
      case_decide; [word | done].
    }
    iClear "Hfpw".
    iFrame "∗ # %".
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
  Qed.

End program.
