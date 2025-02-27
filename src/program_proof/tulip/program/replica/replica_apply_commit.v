From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_terminated replica_multiwrite replica_release.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__applyCommit__replaying
    rp (tsW : u64) pwrsS pwrs clog ilog gid γ α :
    let ts := uint.nat tsW in
    let clog' := clog ++ [CmdCommit ts pwrs] in
    Forall (λ nc, (nc.1 <= length clog)%nat) ilog ->
    valid_pwrs gid pwrs ->
    group_histm_lbs_from_log γ gid clog' -∗
    is_replica_idx rp γ α -∗
    {{{ own_dbmap_in_slice pwrsS pwrs ∗
        own_replica_replaying rp clog ilog α
    }}}
      Replica__applyCommit #rp #tsW (to_val pwrsS)
    {{{ RET #(); 
        own_dbmap_in_slice pwrsS pwrs ∗ 
        own_replica_replaying rp clog' ilog α
    }}}.
  Proof.
    iIntros (ts clog' Hvicmds Hvpwrs) "#Hhistmlb #Hidx".
    iIntros (Φ) "!> [Hpwrs Hrp] HΦ".
    wp_rec.
    (* First establish that applying this commit results does not get stuck. *)
    rewrite /group_histm_lbs_from_log.
    destruct (apply_cmds clog') as [cm' histm' |] eqn:Happly'; last done.
    (* Also establish connection between executing entire log vs. consistent log. *)
    iNamed "Hrp".
    unshelve epose proof (execute_cmds_apply_cmds clog ilog cm histm _) as Happly.
    { by eauto 10. }

    (*@ func (rp *Replica) applyCommit(ts uint64, pwrs []tulip.WriteEntry) {    @*)
    (*@     // Query the transaction table. Note that if there's an entry for @ts in @*)
    (*@     // @txntbl, then transaction @ts can only be committed. That's why we're not @*)
    (*@     // even reading the value of entry.                                 @*)
    (*@     committed := rp.terminated(ts)                                      @*)
    (*@     if committed {                                                      @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__terminated with "Hcm").
    iIntros "Hcm".
    case_bool_decide as Hterm; wp_pures.
    { iApply "HΦ".
      apply elem_of_dom in Hterm as [b Hb].
      iFrame "∗ # %".
      iPureIntro. simpl.
      exists ptgsm.
      rewrite merge_clog_ilog_snoc_clog; last apply Hvicmds.
      rewrite /execute_cmds foldl_snoc /= execute_cmds_unfold Hexec /= Hb.
      destruct b; first done.
      by rewrite /apply_cmds foldl_snoc /= apply_cmds_unfold /apply_commit Happly Hb in Happly'.
    }
    apply not_elem_of_dom in Hterm.
    rewrite /apply_cmds foldl_snoc /= apply_cmds_unfold Happly /= Hterm in Happly'.
    case_decide as Hsafeext; last done.
    symmetry in Happly'. inv Happly'.

    (*@     rp.multiwrite(ts, pwrs)                                             @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__multiwrite with "Hhistmlb Hidx [$Hpwrs $Hhistm]").
    { apply Hvpwrs. }
    { by eapply apply_cmds_dom. }
    { apply Hsafeext. }
    iIntros "[Hpwrs Hhistm]".

    (*@     rp.txntbl[ts] = true                                                @*)
    (*@                                                                         @*)
    iNamed "Hcm".
    wp_loadField.
    wp_apply (wp_MapInsert with "Htxntbl"); first done.
    iIntros "Htxntbl".

    (*@     // With PCR, a replica might receive a commit even if it is not prepared on @*)
    (*@     // this replica.                                                    @*)
    (*@     _, prepared := rp.prepm[ts]                                         @*)
    (*@                                                                         @*)
    iNamed "Hcpm".
    wp_loadField.
    wp_apply (wp_MapGet with "HprepmS").
    iIntros (prepS prepared) "[%Hprepared HprepmS]".
    wp_pures.

    (*@     if prepared {                                                       @*)
    (*@         rp.release(pwrs)                                                @*)
    (*@         delete(rp.prepm, ts)                                            @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    destruct prepared; wp_pures.
    { wp_apply (wp_Replica__release with "[$Hpwrs $Hptsmsptsm]").
      { clear -Hvpwrs. set_solver. }
      iIntros "[Hpwrs Hptsmsptsm]".
      wp_loadField.
      wp_apply (wp_MapDelete with "HprepmS").
      iIntros "HprepmS".
      wp_pures.
      iApply "HΦ".
      apply map_get_true in Hprepared.
      iDestruct (big_sepM2_delete_l with "Hprepm") as (m) "(%Hm & _ & Hprepm)".
      { apply Hprepared. }
      iFrame "∗ #".
      iPureIntro. simpl.
      exists (<[ts := true]> cm), (delete ts cpm), (delete ts ptgsm).
      split.
      { rewrite 2!kmap_insert. f_equal; [word | done]. }
      split.
      { rewrite 2!kmap_delete. f_equal; [word | done]. }
      split.
      { by apply map_Forall_delete. }
      { rewrite merge_clog_ilog_snoc_clog; last apply Hvicmds.
        symmetry in Hcpmabs.
        pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcpmabs Hm) as (ts' & Hts' & Hcpmts).
        assert (ts' = ts) as -> by word.
        rewrite /execute_cmds foldl_snoc /= execute_cmds_unfold Hexec /= Hterm Hcpmts.
        by case_decide.
      }
    }
    iDestruct (big_sepM2_dom with "Hprepm") as %Hdomprepm.
    iApply "HΦ".
    iFrame "∗ # %".
    iPureIntro. simpl.
    exists (<[ts := true]> cm), ptgsm.
    split.
    { rewrite 2!kmap_insert. f_equal; [word | done]. }
    { rewrite merge_clog_ilog_snoc_clog; last apply Hvicmds.
      apply map_get_false in Hprepared as [Hnone _].
      rewrite -not_elem_of_dom Hdomprepm not_elem_of_dom in Hnone.
      symmetry in Hcpmabs.
      pose proof (lookup_kmap_eq_None _ _ _ _ _  Hcpmabs Hnone) as Hcpmnone.
      specialize (Hcpmnone ts).
      unshelve epose proof (Hcpmnone _) as Hcpmts; first word.
      rewrite /execute_cmds foldl_snoc /= execute_cmds_unfold Hexec /= Hterm Hcpmts.
      by case_decide.
    }
  Qed.

  Theorem wp_Replica__applyCommit
    rp (tsW : u64) pwrsS pwrs cloga gid rid γ α :
    let ts := uint.nat tsW in
    let cloga' := cloga ++ [CmdCommit ts pwrs] in
    valid_pwrs gid pwrs ->
    group_histm_lbs_from_log γ gid cloga' -∗
    is_txn_log_lb γ gid cloga' -∗
    is_replica_idx rp γ α -∗
    {{{ own_dbmap_in_slice pwrsS pwrs ∗
        own_replica_with_cloga_no_lsna rp cloga gid rid γ α
    }}}
      Replica__applyCommit #rp #tsW (to_val pwrsS)
    {{{ RET #(); 
        own_dbmap_in_slice pwrsS pwrs ∗ 
        own_replica_with_cloga_no_lsna rp cloga' gid rid γ α
    }}}.
  Proof.
    iIntros (ts cloga' Hvpwrs) "#Hhistmlb #Hlb' #Hidx".
    iIntros (Φ) "!> [Hpwrs Hrp] HΦ".
    wp_rec.
    (* First establish that applying this commit results does not get stuck. *)
    rewrite /group_histm_lbs_from_log.
    destruct (apply_cmds cloga') as [cm' histm' |] eqn:Happly'; last done.
    (* Also establish connection between executing entire log vs. consistent log. *)
    iNamed "Hrp".
    unshelve epose proof (execute_cmds_apply_cmds cloga ilog cm histm _) as Happly.
    { by eauto 10. }

    (*@ func (rp *Replica) applyCommit(ts uint64, pwrs []tulip.WriteEntry) {    @*)
    (*@     // Query the transaction table. Note that if there's an entry for @ts in @*)
    (*@     // @txntbl, then transaction @ts can only be committed. That's why we're not @*)
    (*@     // even reading the value of entry.                                 @*)
    (*@     committed := rp.terminated(ts)                                      @*)
    (*@     if committed {                                                      @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__terminated with "Hcm").
    iIntros "Hcm".
    case_bool_decide as Hterm; wp_pures.
    { iApply "HΦ".
      apply elem_of_dom in Hterm as [b Hb].
      iFrame "∗ # %".
      iPureIntro. simpl.
      exists ptgsm.
      split.
      { by apply prefix_app_r. }
      rewrite merge_clog_ilog_snoc_clog; last apply Hvicmds.
      split.
      { eapply Forall_impl; first apply Hvicmds. simpl.
        intros nc Hnc.
        rewrite length_app /=.
        clear -Hnc. lia.
      }
      rewrite /execute_cmds foldl_snoc /= execute_cmds_unfold Hexec /= Hb.
      destruct b; first done.
      by rewrite /apply_cmds foldl_snoc /= apply_cmds_unfold /apply_commit Happly Hb in Happly'.
    }
    apply not_elem_of_dom in Hterm.
    rewrite /apply_cmds foldl_snoc /= apply_cmds_unfold Happly /= Hterm in Happly'.
    case_decide as Hsafeext; last done.
    symmetry in Happly'. inv Happly'.

    (*@     rp.multiwrite(ts, pwrs)                                             @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__multiwrite with "Hhistmlb Hidx [$Hpwrs $Hhistm]").
    { apply Hvpwrs. }
    { by eapply apply_cmds_dom. }
    { apply Hsafeext. }
    iIntros "[Hpwrs Hhistm]".

    (*@     rp.txntbl[ts] = true                                                @*)
    (*@                                                                         @*)
    iNamed "Hcm".
    wp_loadField.
    wp_apply (wp_MapInsert with "Htxntbl"); first done.
    iIntros "Htxntbl".

    (*@     // With PCR, a replica might receive a commit even if it is not prepared on @*)
    (*@     // this replica.                                                    @*)
    (*@     _, prepared := rp.prepm[ts]                                         @*)
    (*@                                                                         @*)
    iNamed "Hcpm".
    wp_loadField.
    wp_apply (wp_MapGet with "HprepmS").
    iIntros (prepS prepared) "[%Hprepared HprepmS]".
    wp_pures.

    (*@     if prepared {                                                       @*)
    (*@         rp.release(pwrs)                                                @*)
    (*@         delete(rp.prepm, ts)                                            @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    destruct prepared; wp_pures.
    { wp_apply (wp_Replica__release with "[$Hpwrs $Hptsmsptsm]").
      { clear -Hvpwrs. set_solver. }
      iIntros "[Hpwrs Hptsmsptsm]".
      wp_loadField.
      wp_apply (wp_MapDelete with "HprepmS").
      iIntros "HprepmS".
      wp_pures.
      iApply "HΦ".
      apply map_get_true in Hprepared.
      iDestruct (big_sepM2_delete_l with "Hprepm") as (m) "(%Hm & _ & Hprepm)".
      { apply Hprepared. }
      iAssert ([∗ set] t ∈ dom (delete ts cpm), is_replica_validated_ts γ gid rid t)%I
        as "#Hrpvds'".
      { rewrite dom_delete_L.
        iDestruct (big_sepS_delete _ _ ts with "Hrpvds") as "[_ ?]"; last done.
        symmetry in Hcpmabs.
        pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcpmabs Hm) as (ts' & Hts' & Hcpmts).
        assert (ts' = ts) as -> by word.
        by apply elem_of_dom.
      }
      iClear "Hrpvds".
      iFrame "∗ # %".
      iPureIntro. simpl.
      exists (<[ts := true]> cm), (delete ts ptgsm).
      split.
      { rewrite 2!kmap_insert. f_equal; [word | done]. }
      split.
      { rewrite 2!kmap_delete. f_equal; [word | done]. }
      split.
      { by apply prefix_app_r. }
      { rewrite merge_clog_ilog_snoc_clog; last apply Hvicmds.
        split.
        { by apply map_Forall_delete. }
        split.
        { eapply Forall_impl; first apply Hvicmds. simpl.
          intros nc Hnc.
          rewrite length_app /=.
          clear -Hnc. lia.
        }
        symmetry in Hcpmabs.
        pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcpmabs Hm) as (ts' & Hts' & Hcpmts).
        assert (ts' = ts) as -> by word.
        rewrite /execute_cmds foldl_snoc /= execute_cmds_unfold Hexec /= Hterm Hcpmts.
        by case_decide.
      }
    }
    iDestruct (big_sepM2_dom with "Hprepm") as %Hdomprepm.
    iApply "HΦ".
    iFrame "∗ # %".
    iPureIntro. simpl.
    exists (<[ts := true]> cm), ptgsm.
    split.
    { rewrite 2!kmap_insert. f_equal; [word | done]. }
    split.
    { by apply prefix_app_r. }
    { rewrite merge_clog_ilog_snoc_clog; last apply Hvicmds.
      split.
      { eapply Forall_impl; first apply Hvicmds. simpl.
        intros nc Hnc.
        rewrite length_app /=.
        clear -Hnc. lia.
      }
      apply map_get_false in Hprepared as [Hnone _].
      rewrite -not_elem_of_dom Hdomprepm not_elem_of_dom in Hnone.
      symmetry in Hcpmabs.
      pose proof (lookup_kmap_eq_None _ _ _ _ _  Hcpmabs Hnone) as Hcpmnone.
      specialize (Hcpmnone ts).
      unshelve epose proof (Hcpmnone _) as Hcpmts; first word.
      rewrite /execute_cmds foldl_snoc /= execute_cmds_unfold Hexec /= Hterm Hcpmts.
      by case_decide.
    }
  Qed.

End program.
