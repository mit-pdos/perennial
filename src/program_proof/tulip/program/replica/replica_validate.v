From Perennial.program_proof.tulip.invariance Require Import execute validate.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_finalized replica_try_acquire replica_memorize
  replica_refresh replica_log.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__validate
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
      Replica__validate #rp #tsW (to_val pwrsS) (to_val ptgsS)
    {{{ (res : rpres), RET #(rpres_to_u64 res);
        own_replica rp gid rid γ α ∗ validate_outcome γ gid rid ts res
    }}}.
  Proof.
    iIntros (ts Hgid Hrid) "#Hlnrz #Hsafepwrs #Hsafeptgs #Hpwrs #Hptgs #Hinv #Hinvfile".
    iIntros (Φ) "!> Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) validate(ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) uint64 { @*)
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

    (*@     // Check if the replica has already validated this transaction.     @*)
    (*@     _, validated := rp.prepm[ts]                                        @*)
    (*@     if validated {                                                      @*)
    (*@         return tulip.REPLICA_OK                                         @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hrp". iNamed "Hcpm".
    iDestruct (big_sepM2_dom with "Hprepm") as %Hdomprepm.
    wp_loadField.
    wp_apply (wp_MapGet with "HprepmS").
    iIntros (prepS validated) "[%Hvalidated HprepmS]".
    wp_pures.
    destruct validated; wp_pures.
    { apply map_get_true in Hvalidated.
      iApply ("HΦ" $! ReplicaOK).
      assert (Hin : ts ∈ dom cpm).
      { apply elem_of_dom_2 in Hvalidated.
        rewrite Hdomprepm elem_of_dom in Hvalidated.
        destruct Hvalidated as [b Hb].
        symmetry in Hcpmabs.
        pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcpmabs Hb) as (ts' & Hts' & Hin).
        assert (ts' = ts) as ->.
        { subst ts. rewrite Hts'. lia. }
        by apply elem_of_dom_2 in Hin.
      }
      iDestruct (big_sepS_elem_of with "Hrpvds") as "#Hrpvd"; first apply Hin.
      by iFrame "∗ # %".
    }

    (*@     // Validate timestamps.                                             @*)
    (*@     acquired := rp.tryAcquire(ts, pwrs)                                 @*)
    (*@     if !acquired {                                                      @*)
    (*@         return tulip.REPLICA_FAILED_VALIDATION                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iDestruct (safe_txn_pwrs_dom_pwrs with "Hsafepwrs") as %Hdompwrs.
    wp_apply (wp_Replica__tryAcquire with "Hpwrs Hptsmsptsm").
    { apply Hdompwrs. }
    iIntros (acquired) "Hptsmsptsm".
    wp_pures.
    destruct acquired; wp_pures; last first.
    { iApply ("HΦ" $! ReplicaFailedValidation). by iFrame "∗ # %". }
    iDestruct "Hptsmsptsm" as "(Hptsmsptsm & %Hvptsm & %Hvsptsm)".

    (* Normally we log at the end to save one [iApply ncfupd_wp], but
    since @rp.memorize consumes the ownership of [Hpwrs], we log one step
    earlier. *)

    (*@     // Logical action: Validate(@ts, @pwrs, @ptgs).                     @*)
    (*@     logAcquire(rp.fname, rp.lsna, ts, pwrs, ptgs)                       @*)
    (*@                                                                         @*)
    wp_pures.
    iNamed "Hlsna".
    wp_loadField.
    iNamed "Hfname".
    wp_loadField.
    wp_apply (wp_logAcquire with "Hpwrs Hptgs").
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
    split; first done.
    rewrite merge_clog_ilog_snoc_ilog; last done.
    split.
    { by apply map_Forall_insert_2. }
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

  Theorem wp_Replica__Validate
    rp (tsW rankW : u64) pwrsS pwrs ptgsS ptgs gid rid γ :
    let ts := uint.nat tsW in
    is_lnrz_tid γ ts -∗
    safe_txn_pwrs γ gid ts pwrs -∗
    safe_txn_ptgs γ ts ptgs -∗
    is_dbmap_in_slice pwrsS pwrs -∗
    is_txnptgs_in_slice ptgsS ptgs -∗
    is_replica rp gid rid γ -∗
    {{{ True }}}
      Replica__Validate #rp #tsW #rankW (to_val pwrsS) (to_val ptgsS)
    {{{ (res : rpres), RET #(rpres_to_u64 res);
        validate_outcome γ gid rid ts res
    }}}.
  Proof.
    iIntros (ts) "#Hlnrz #Hsafepwrs #Hsafeptgs #Hpwrs #Hptgs #Hrp".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) Validate(ts uint64, rank uint64, pwrs []tulip.WriteEntry, ptgs []uint64) uint64 { @*)
    (*@     rp.mu.Lock()                                                        @*)
    (*@     res := rp.validate(ts, pwrs, ptgs)                                  @*)
    (*@     rp.refresh(ts, rank)                                                @*)
    (*@     rp.mu.Unlock()                                                      @*)
    (*@     return res                                                          @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hrp]".
    iNamed "Hgidrid".
    wp_apply (wp_Replica__validate with "Hlnrz Hsafepwrs Hsafeptgs Hpwrs Hptgs [$Hinv] Hinvfile Hrp").
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
