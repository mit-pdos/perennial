From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import auth.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant wal.common_proof.

Remove Hints fractional.into_sep_fractional : typeclass_instances.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names).
Implicit Types (s: log_state.t) (memLog: slidingM.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let innerN := walN .@ "wal".
Let circN := walN .@ "circ".

Theorem wp_Walog__waitForSpace l γ σₛ :
  {{{ "#HmemLock" ∷ readonly (l ↦[Walog.S :: "memLock"] #σₛ.(memLock)) ∗
      "#HcondLogger" ∷ readonly (l ↦[Walog.S :: "condLogger"] #σₛ.(condLogger)) ∗
      "#HcondInstall" ∷ readonly (l ↦[Walog.S :: "condInstall"] #σₛ.(condInstall)) ∗
      "#His_cond1" ∷ is_cond σₛ.(condLogger) #σₛ.(memLock) ∗
      "#His_cond2" ∷ is_cond σₛ.(condInstall) #σₛ.(memLock) ∗
      "#?" ∷ readonly (l ↦[Walog.S :: "st"] #σₛ.(wal_st)) ∗
      "Hlkinv" ∷ wal_linv σₛ.(wal_st) γ ∗
      "Hlocked" ∷ locked #σₛ.(memLock) ∗
      "#His_lock" ∷ is_lock N #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ)
  }}}
    Walog__waitForSpace #l
  {{{ σ, RET #();
      "Hlocked" ∷ locked #σₛ.(memLock)  ∗
      "Hfields" ∷ wal_linv_fields σₛ.(wal_st) σ ∗
      "HmemLog_linv" ∷ memLog_linv γ σ.(memLog) σ.(diskEnd) σ.(locked_diskEnd_txn_id) ∗
      "HdiskEnd_circ" ∷ diskEnd_linv γ σ.(diskEnd) σ.(locked_diskEnd_txn_id) ∗
      "Hstart_circ" ∷ diskStart_linv γ σ.(memLog).(slidingM.start) ∗
      "%Hhas_space" ∷ ⌜length σ.(memLog).(slidingM.log) ≤ LogSz⌝
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  iNamed "Hlkinv".
  wp_apply (wp_forBreak_cond
              (λ b, "Hlocked" ∷ locked #σₛ.(memLock) ∗
                    "*" ∷ ∃ σ, "Hfields" ∷ wal_linv_fields σₛ.(wal_st) σ ∗
                               "HmemLog_linv" ∷ memLog_linv γ σ.(memLog) σ.(diskEnd) σ.(locked_diskEnd_txn_id) ∗
                               "HdiskEnd_circ" ∷ diskEnd_linv γ σ.(diskEnd) σ.(locked_diskEnd_txn_id) ∗
                               "Hstart_circ" ∷ diskStart_linv γ σ.(memLog).(slidingM.start) ∗
                               "%Hbreak" ∷ ⌜b = false → (length σ.(memLog).(slidingM.log) ≤ LogSz)⌝
              )%I
              with "[] [-HΦ]").
  2: {
    iFrame.
    iExists _; iFrame "# ∗".
    iPureIntro. inversion 1.
  }
  { iIntros "!>" (Φ') "HI HΦ".
    iNamed "HI".
    iNamed "Hfields".
    iNamed "Hfield_ptsto".
    wp_loadField. wp_loadField.
    wp_apply (wp_log_len with "His_memLog"); iIntros "His_memLog".
    wp_pures.
    change (int.Z (word.divu (word.sub 4096 8) 8)) with LogSz.
    wp_if_destruct.
    - wp_loadField.
      wp_apply (wp_condWait with "[-HΦ]"); [ iFrame "His_cond2 His_lock Hlocked" | ].
      { iExists _; iFrame "∗ #". iExists _; iFrame "% # ∗". }
      iIntros "(Hlocked&Hlkinv)".
      wp_pures.
      iApply "HΦ"; iFrame.
      iNamed "Hlkinv".
      iExists _; iFrame "# ∗".
      iPureIntro; inversion 1.
    - iApply "HΦ"; iFrame.
      iExists _; iFrame "∗ #".
      iSplit.
      { iExists _; by iFrame "# ∗". }
      iPureIntro.
      intros _.
      unfold locked_wf, slidingM.wf in Hlocked_wf.
      revert Heqb; word.
  }
  iIntros "HI"; iNamed "HI".
  specialize (Hbreak ltac:(auto)).
  iApply "HΦ".
  iFrameNamed. auto.
Qed.

Hint Unfold slidingM.logIndex slidingM.wf : word.

Lemma circ_matches_extend cs txns installed_txn_id diskEnd_txn_id new_txn nextDiskEnd_txn_id :
  (installed_txn_id ≤ diskEnd_txn_id ≤ nextDiskEnd_txn_id)%nat →
  (nextDiskEnd_txn_id < length txns)%nat →
  has_updates new_txn (subslice (S diskEnd_txn_id) (S nextDiskEnd_txn_id) txns) →
  circ_matches_txns cs txns installed_txn_id diskEnd_txn_id →
  circ_matches_txns (set upds (λ u, u ++ new_txn) cs) txns installed_txn_id nextDiskEnd_txn_id.
Proof.
  rewrite /circ_matches_txns /=.
  intros ? ? ? [? ?].
  split; [ | lia ].
  rewrite -> (subslice_split_r installed_txn_id (S diskEnd_txn_id) (S nextDiskEnd_txn_id)) by lia.
  apply has_updates_app; auto.
Qed.

Lemma is_installed_extend_durable γ d txns installed_txn_id diskEnd_txn_id diskEnd_txn_id' :
  (diskEnd_txn_id ≤ diskEnd_txn_id' < length txns)%nat →
  is_installed γ d txns installed_txn_id diskEnd_txn_id -∗
  is_installed γ d txns installed_txn_id diskEnd_txn_id'.
Proof.
  intros Hbound.
  iNamed 1.
  iExists _, _; iFrame.
  iPureIntro; lia.
Qed.

Lemma circ_diskEnd_app σ upds' :
  circΣ.diskEnd (set circΣ.upds (λ u, u ++ upds') σ) =
  circΣ.diskEnd σ + length upds'.
Proof.
  rewrite /circΣ.diskEnd /=.
  len.
Qed.

Lemma logIndex_diff memLog pos1 pos2 :
  int.Z memLog.(slidingM.start) ≤ int.Z pos1 →
  (slidingM.logIndex memLog pos2 - slidingM.logIndex memLog pos1)%nat =
  (int.nat pos2 - int.nat pos1)%nat.
Proof.
  rewrite /slidingM.logIndex; intros.
  lia.
Qed.

Theorem wp_Walog__logAppend l circ_l γ dinit σₛ :
  {{{ "#HmemLock" ∷ readonly (l ↦[Walog.S :: "memLock"] #σₛ.(memLock)) ∗
      "#HcondLogger" ∷ readonly (l ↦[Walog.S :: "condLogger"] #σₛ.(condLogger)) ∗
      "#HcondInstall" ∷ readonly (l ↦[Walog.S :: "condInstall"] #σₛ.(condInstall)) ∗
      "#d" ∷ readonly (l ↦[Walog.S :: "d"] σₛ.(wal_d)) ∗
      "#circ" ∷ readonly (l ↦[Walog.S :: "circ"] #σₛ.(circ)) ∗
      "#His_cond1" ∷ is_cond σₛ.(condLogger) #σₛ.(memLock) ∗
      "#His_cond2" ∷ is_cond σₛ.(condInstall) #σₛ.(memLock) ∗
      "#?" ∷ readonly (l ↦[Walog.S :: "st"] #σₛ.(wal_st)) ∗
      "#His_lock" ∷ is_lock N #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ) ∗
      "#Hwal" ∷ is_wal P l γ dinit ∗
      "Hlkinv" ∷ wal_linv σₛ.(wal_st) γ ∗
      "Hlocked" ∷ locked #σₛ.(memLock) ∗
      "Hlogger" ∷ logger_inv γ circ_l
  }}}
    Walog__logAppend #l #circ_l
  {{{ (progress:bool), RET #progress;
      wal_linv σₛ.(wal_st) γ ∗
      locked #σₛ.(memLock) ∗
      logger_inv γ circ_l
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ"; iNamed "Hpre".
  iNamed "Hlogger".
  wp_call.
  wp_apply (wp_Walog__waitForSpace with "[$Hlkinv $Hlocked]").
  { iFrameNamed. iFrame "#". }
  iIntros (σ) "Hpost"; iNamed "Hpost".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  wp_loadField. wp_loadField.
  wp_loadField. wp_loadField.
  wp_apply (wp_sliding__takeFrom with "His_memLog").
  { word. }
  iIntros (q s) "(His_memLog&Hbufs)".
  wp_pures.
  wp_apply wp_slice_len; wp_pures.
  wp_if_destruct; wp_pures.
  { iApply "HΦ".
    iFrame "Hlocked".
    iSplitR "HnotLogging Happender HownLoggerPos_logger HownLoggerTxn_logger".
    - iExists _; iFrame.
      iExists _; iFrame "% ∗".
    - iFrame.
  }
  iNamed "HdiskEnd_circ".
  iMod (thread_own_get with "HdiskEnd_exactly HnotLogging") as
      "(HdiskEnd_exactly&Hlog_owned&HareLogging)";
    iNamed "Hlog_owned".
  iNamed "HmemLog_linv".
  iNamed "HnextDiskEnd".
  iNamed "Hstart_circ".
  iMod (txn_pos_valid_locked with "Hwal HmemStart_txn Howntxns") as "(%HmemStart_txn&Howntxns)".
  iMod (txn_pos_valid_locked with "Hwal HnextDiskEnd_txn Howntxns") as "(%HnextDiskEnd_txn&Howntxns)".
  iMod (get_txns_are _ _ _ _ _ memStart_txn_id (S nextDiskEnd_txn_id) with "Howntxns Hwal") as "[Htxns_are Howntxns]"; eauto.
  { pose proof (is_txn_bound _ _ _ HnextDiskEnd_txn).
    lia. }

  (* snapshot the position we're about to write to circular log *)
  iNamed "HownLoggerPos_logger".
  iMod (ghost_var_update_halves σ.(memLog).(slidingM.mutable) with "HownLoggerPos_logger HownLoggerPos_linv") as
        "[HownLoggerPos_logger HownLoggerPos_linv]".
  iNamed "HownLoggerTxn_logger".
  iMod (ghost_var_update_halves nextDiskEnd_txn_id with "HownLoggerTxn_logger HownLoggerTxn_linv") as
        "[HownLoggerTxn_logger HownLoggerTxn_linv]".

  iAssert (ghost_var γ.(txns_name) (1 / 2) txns ={⊤}=∗ ghost_var γ.(txns_name) (1 / 2) txns ∗ txn_pos γ σ.(locked_diskEnd_txn_id) σ.(diskEnd))%I as "HdiskEnd_pos_helper".
  {
    iIntros "Howntxns".
    iDestruct "Hwal" as "[Hwal Hcirc]".
    iInv "Hwal" as (σs) "[Hinner HP]".
    iDestruct "Hinner" as "(>%Hwf&Hmem&>?&>?&>?&>?)"; iNamed.
    iDestruct (ghost_var_agree with "Howntxns γtxns") as %->.
    iDestruct (txns_ctx_txn_pos with "Htxns_ctx") as "#HdiskEnd_pos".
    1: apply HdiskEnd_txn.
    iModIntro.
    iFrame "HdiskEnd_pos Howntxns".
    iSplitL; try done.
    iModIntro. iExists _. iFrame. iFrame "%".
  }
  iMod ("HdiskEnd_pos_helper" with "Howntxns") as "[Howntxns #HdiskEnd_pos]".

  iNamed "Htxns".

  (* use this to also strip a later, which the [wp_loadField] tactic does not do *)
  wp_apply (wp_loadField_ro with "HmemLock").
  iDestruct "Htxns_are" as "#Htxns_are".
  wp_apply (release_spec with "[-HΦ HareLogging HdiskEnd_is Happender Hbufs $His_lock $Hlocked HownLoggerPos_logger HownLoggerTxn_logger]").
  {
    iExists _; iFrame "# % ∗".
    iSplitR "Howntxns HmemEnd_txn HownStableSet HownLoggerPos_linv HownLoggerTxn_linv".
    - iExists _; iFrame "% ∗".
    - iExists _, _, _, _, _, _.
      iFrame "HownLoggerPos_linv HownLoggerTxn_linv".
      iFrame "# % ∗".
      iModIntro.
      iSplitR.
      { iPureIntro. lia. }
      iSplitL "HownStableSet".
      { iExists _. iFrame. iFrame "%". }
      iSplit.
      { iPureIntro. lia. }
      iSplit.
      2: { rewrite ?subslice_zero_length. done. }
      iPureIntro.
      rewrite -> (subslice_split_r (slidingM.logIndex σ.(memLog) σ.(diskEnd)) (slidingM.logIndex σ.(memLog) logger_pos)) by word.
      rewrite -> (subslice_split_r (S σ.(locked_diskEnd_txn_id)) (S logger_txn_id)); [ | lia | ].
      2: { pose proof (is_txn_bound _ _ _ HnextDiskEnd_txn). lia. }
      eapply has_updates_app; eauto.
  }
  wp_loadField.
  iDestruct "Hwal" as "[Hwal Hcirc]".

  wp_apply (wp_circular__Append _ _
                              (True)
              with "[$Hbufs $HdiskEnd_is $Happender $Hcirc $Hstart_at_least]").
  { rewrite subslice_length; word. }
  { rewrite subslice_length; word. }

  { (* Append fupd *)
    rewrite /circular_pred.
    iIntros (cs) "(%Hcirc_wf&%HdiskEnd_eq&Hcirc_ctx)".
    iIntros (cs' [] [Htrans Hcirc_wf']).
    simpl in Htrans; monad_inv.
    iInv "Hwal" as (σs) "[Hinner HP]".

    iDestruct "Hinner" as "(>%Hwf&Hmem&>?&>?&>?&>?)"; iNamed.
    iNamed "Hdisk".
    iNamed "Hdisk".
    iDestruct (ghost_var_agree with "Hcirc_ctx Howncs") as %Heq; subst cs0.
    iDestruct (txns_are_sound with "Htxns_ctx Htxns_are") as %Htxns_are.
    iDestruct (txn_pos_valid_general with "Htxns_ctx HmemStart_txn") as %HmemStart'.
    iDestruct (txn_pos_valid_general with "Htxns_ctx HnextDiskEnd_txn") as %HnextDiskEnd'.
    iMod (ghost_var_update_halves with "Hcirc_ctx Howncs") as "[$ Howncs]".

    iDestruct (txn_pos_valid_general with "Htxns_ctx HdiskEnd_pos") as %HdiskEnd_pos.
    iNamed "circ.end".

    rewrite HdiskEnd_eq in HdiskEnd_val.
    assert (diskEnd = σ.(invariant.diskEnd)) by word; subst.
    iDestruct (subslice_stable_nils2 with "[$HnextDiskEnd_inv $HdiskEnd_stable]") as "%HdiskEnd_nils_1";
      [ eauto | apply HdiskEnd_pos | apply Hend_txn | ].
    iDestruct (subslice_stable_nils2 with "[$HnextDiskEnd_inv $Hend_txn_stable]") as "%HdiskEnd_nils_2";
      [ eauto | apply Hend_txn | apply HdiskEnd_pos | ].

    iModIntro.
    iSplitL; eauto.
    iNext.
    iExists _; iFrame.
    iSplitR; auto.
    iExists _; iFrame.
    iExists installed_txn_id, (Nat.max diskEnd_txn_id nextDiskEnd_txn_id).
    iFrame "# % ∗".
    iSplitL "Hinstalled".
    { iApply (is_installed_extend_durable with "Hinstalled").
      apply is_txn_bound in HnextDiskEnd'.
      apply is_txn_bound in Hend_txn. lia. }
    iSplitL "Hdurable".
    { iDestruct "Hdurable" as %Hmatches.
      iPureIntro.
      eapply circ_matches_extend; eauto; try lia.
      { split; try lia.
        destruct Hmatches. done. }
      { apply is_txn_bound in HnextDiskEnd'.
        apply is_txn_bound in Hend_txn. lia. }
      pose proof (is_txn_bound _ _ _ HnextDiskEnd_txn).
      rewrite -> subslice_length in Htxns_are by lia.
      replace (memStart_txn_id + (S nextDiskEnd_txn_id - memStart_txn_id))%nat
              with (S nextDiskEnd_txn_id) in Htxns_are by lia.
      apply (subslice_suffix_eq _ _ _ (S σ.(locked_diskEnd_txn_id))) in Htxns_are; last by lia.

      pose proof (has_updates_app _ _ _ _ His_loggerEnd His_nextDiskEnd) as His_logger.
      rewrite <- subslice_split_r in His_logger; try word.
      rewrite <- subslice_split_r in His_logger; try word.

      rewrite -Htxns_are in His_logger.
      pose proof (is_txn_bound _ _ _ HnextDiskEnd').

      destruct (decide (diskEnd_txn_id ≤ nextDiskEnd_txn_id)).
      { rewrite max_r; last by lia.
        destruct (decide (σ.(locked_diskEnd_txn_id) ≤ diskEnd_txn_id)).
        {
          eapply has_updates_prepend_nils; first by apply HdiskEnd_nils_1.
          rewrite <- subslice_split_r; eauto; intuition lia.
        }
        {
          erewrite -> (subslice_split_r (S diskEnd_txn_id) (S σ.(locked_diskEnd_txn_id))) by lia.
          eapply has_updates_prepend_nils_2; first by apply HdiskEnd_nils_2.
          eauto.
        }
      }
      rewrite max_l; last by lia.

      assert (int.Z σ.(memLog).(slidingM.mutable) ≤ int.Z σ.(diskEnd)) as HdiskEnd_le_mutable.
      { eapply wal_wf_txns_mono_pos'; eauto. lia. }
      assert (σ.(memLog).(slidingM.mutable) = σ.(diskEnd)) as HdiskEnd_eq_mutable by word.
      rewrite HdiskEnd_eq_mutable.
      rewrite ?subslice_zero_length. done.
    }
    rewrite /is_durable_txn.
    iExists σ.(memLog).(slidingM.mutable).
    iSplit.
    { iPureIntro.
      lia. }
    iSplit.
    { iPureIntro.
      simpl.
      rewrite circ_diskEnd_app.
      rewrite -> subslice_length by word.
      rewrite -> logIndex_diff by word.
      word. }

    destruct (decide (diskEnd_txn_id ≤ nextDiskEnd_txn_id)).
    { rewrite max_r; last by lia. iFrame "#". iPureIntro; eauto. }
    rewrite max_l; last by lia. iFrame "#".
    assert (int.Z σ.(memLog).(slidingM.mutable) ≤ int.Z σ.(diskEnd)) as HdiskEnd_le_mutable.
    { eapply wal_wf_txns_mono_pos'; eauto. lia. }
    assert (σ.(memLog).(slidingM.mutable) = σ.(diskEnd)) as HdiskEnd_eq_mutable by word.
    rewrite HdiskEnd_eq_mutable.
    iPureIntro. eauto.
  }
  rewrite -> subslice_length by word.
  iIntros "(Hpost&Hupds&Hcirc_appender&HdiskEnd_is)"; iNamed "Hpost".
  wp_loadField.
  wp_apply (acquire_spec with "His_lock").
  iIntros "(His_locked&Hlockinv)".
  iNamed "Hlockinv".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".

  (* Open up memlog lock invariant to prove we still have the same logger pos *)
  iRename "HmemStart_txn" into "HmemStart_txn_old".
  iRename "HdiskEnd_stable" into "HdiskEnd_stable_old".
  iRename "HnextDiskEnd_txn" into "HnextDiskEnd_txn_old".
  iRename "HnextDiskEnd_stable" into "HnextDiskEnd_stable_old".
  iRename "HmemEnd_txn" into "HmemEnd_txn_old".
  iRename "Hinstalled_txn_id_bound" into "Hinstalled_txn_id_bound_old".
  iNamed "HmemLog_linv".
  iDestruct (ghost_var_agree with "HownLoggerPos_linv HownLoggerPos_logger") as %Heqloggerpos; subst.
  iDestruct (ghost_var_agree with "HownLoggerTxn_linv HownLoggerTxn_logger") as %Heqloggertxn; subst.

  iAssert (ghost_var γ.(txns_name) (1 / 2) txns0 ={⊤}=∗
           ghost_var γ.(txns_name) (1 / 2) txns0 ∗
           ⌜is_txn txns0 nextDiskEnd_txn_id σ.(memLog).(slidingM.mutable)⌝ ∗
           ⌜subslice memStart_txn_id (S nextDiskEnd_txn_id) txns0 =
            subslice memStart_txn_id (S nextDiskEnd_txn_id) txns⌝)%I
    as "Htxns0_helper".
  {
    iIntros "Howntxns".
    iInv "Hwal" as (σs) "[Hinner HP]".
    iDestruct "Hinner" as "(>%Hwf&Hmem&>?&>?&>?&>?)"; iNamed.
    iDestruct (ghost_var_agree with "Howntxns γtxns") as %->.
    iFrame "Howntxns".
    iDestruct (txn_pos_valid_general with "Htxns_ctx HnextDiskEnd_txn_old") as %H.
    iDestruct (txns_are_sound with "Htxns_ctx Htxns_are") as %Htxns.
    replace (memStart_txn_id + length (subslice memStart_txn_id (S nextDiskEnd_txn_id) txns))%nat with (S nextDiskEnd_txn_id) in Htxns.
    2: {
      rewrite subslice_length; try lia.
      pose proof (is_txn_bound _ _ _ HnextDiskEnd_txn). lia.
    }
    iModIntro. iSplitL; last by done. iModIntro. iExists _. iFrame. iFrame "%".
  }
  iMod ("Htxns0_helper" with "Howntxns") as "(Howntxns & %HnextDiskEnd_txns0 & %Htxns)".

  iRename "HdiskEnd_at_least" into "HdiskEnd_at_least_old".
  iDestruct (diskEnd_is_to_at_least with "HdiskEnd_is") as "#HdiskEnd_at_least_new".
  iNamed "HdiskEnd_circ".
  iMod (thread_own_put with "HdiskEnd_exactly HareLogging [HdiskEnd_is]")
    as "[HdiskEnd_exactly HnotLogging]"; first by iAccu.
  wp_apply wp_slice_len.
  wp_loadField. wp_storeField.
  wp_loadField.
  wp_apply (wp_condBroadcast with "His_cond1").
  wp_loadField.
  wp_apply (wp_condBroadcast with "His_cond2").
  wp_pures.
  iApply "HΦ".
  iFrame "His_locked".
  iSplitR "Hcirc_appender HnotLogging HownLoggerPos_logger HownLoggerTxn_logger".
  - iExists (set diskEnd (λ _, int.Z σ.(diskEnd) + int.Z s.(Slice.sz))
            (set locked_diskEnd_txn_id (λ _, nextDiskEnd_txn_id) σ0)).
    iDestruct (updates_slice_frag_len with "Hupds") as "%Hupds_len".
    rewrite subslice_length in Hupds_len; last by word.
    rewrite logIndex_diff in Hupds_len; last by word.
    simpl.
    iFrame.
    iSplitL "HmemLog Hshutdown Hnthread His_memLog".
    { iExists _. iFrame.
      iPureIntro.
      rewrite Hupds_len.
      unfold locked_wf in *. simpl.
      intuition try lia.
      { word. }
      { word. }
    }
    iSplitR "Howntxns HnextDiskEnd HownLoggerPos_linv HownLoggerTxn_linv".
    {
      repeat rewrite logIndex_diff; last by word.
      iSplitR "HdiskEnd_exactly".
      2: {
        rewrite Hupds_len.
        replace (int.Z
            (int.Z σ.(diskEnd) +
             (int.nat σ.(memLog).(slidingM.mutable) - int.nat σ.(diskEnd))%nat)) with
          (int.Z σ.(diskEnd) +
                           (int.nat σ.(memLog).(slidingM.mutable) -
                            int.nat σ.(diskEnd))%nat).
        { iFrame. }
        word.
      }
      rewrite Hupds_len.
      replace (int.Z
       (int.Z σ.(diskEnd) +
        (int.nat σ.(memLog).(slidingM.mutable) - int.nat σ.(diskEnd))%nat))
        with (int.Z σ.(diskEnd) +
                             (int.nat σ.(memLog).(slidingM.mutable) -
                              int.nat σ.(diskEnd))%nat) by word.
      iFrame "HdiskEnd_at_least_new".
    }

    iNamed "Htxns".
    iExists _, _, nextDiskEnd_txn_id0, _, _, _.
    iFrame.
    iFrame "HmemStart_txn HmemEnd_txn".
    iFrame "HnextDiskEnd_stable_old".
    iFrame "Hinstalled_txn_id_bound".

    iSplit.
    { iPureIntro. lia. }
    iSplit.
    { rewrite Hupds_len.
      replace (U64 (int.Z σ.(diskEnd) + (int.nat σ.(memLog).(slidingM.mutable) - int.nat σ.(diskEnd))%nat))
        with (σ.(memLog).(slidingM.mutable)) by word.
      done.
    }
    iSplit.
    { rewrite Hupds_len.
      replace (U64 (int.Z σ.(diskEnd) + (int.nat σ.(memLog).(slidingM.mutable) - int.nat σ.(diskEnd))%nat))
        with (σ.(memLog).(slidingM.mutable)) by word.
      iPureIntro. word.
    }
    iSplit.
    2: done.
    iFrame "%".
    iSplit.
    2: {
      rewrite !Hupds_len.
      replace (U64 (int.Z σ.(diskEnd) + (int.nat σ.(memLog).(slidingM.mutable) - int.nat σ.(diskEnd))%nat))
        with (σ.(memLog).(slidingM.mutable)) by word.
      rewrite ?subslice_zero_length.
      done.
    }
    eapply is_txn_bound in HdiskEnd_txn0.
    pose proof (has_updates_app _ _ _ _ His_memStart0 His_loggerEnd0) as His_memStart_new.
    rewrite subslice_take_drop in His_memStart_new.

    replace (take (slidingM.logIndex σ0.(memLog) σ0.(diskEnd)) σ0.(memLog).(slidingM.log))
      with (take (slidingM.logIndex σ0.(memLog) σ0.(diskEnd))
        (take (slidingM.logIndex σ0.(memLog) σ.(memLog).(slidingM.mutable)) σ0.(memLog).(slidingM.log)))
      in His_memStart_new.
    2: {
      rewrite take_take.
      rewrite min_l; eauto.
      rewrite /slidingM.logIndex. word. }
    rewrite take_drop in His_memStart_new.

    rewrite (subslice_split_r (memStart_txn_id0) (S σ0.(locked_diskEnd_txn_id)) (S nextDiskEnd_txn_id) txns0); try lia.
    iPureIntro.
    rewrite Hupds_len.
    replace (int.Z σ.(diskEnd) +
         (int.nat σ.(memLog).(slidingM.mutable) - int.nat σ.(diskEnd))%nat : u64)
      with (σ.(memLog).(slidingM.mutable)) by word.
    eauto.
  - iFrame.
    iSplitL "HownLoggerPos_logger".
    + iExists _; iFrame.
    + iExists _; iFrame.
Qed.

Theorem wp_Walog__logger l circ_l γ dinit :
  {{{ "#Hwal" ∷ is_wal P l γ dinit ∗
      "Hlogger" ∷ logger_inv γ circ_l
  }}}
    Walog__logger #l #circ_l
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hpre HΦ"; iNamed "Hpre".
  iMod (is_wal_read_mem with "Hwal") as "#Hmem".
  wp_call.
  iNamed "Hmem".
  iNamed "Hstfields".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "(Hlk_held&Hlkinv)".
  wp_pures.

  wp_apply (wp_inc_nthread with "[$st $Hlkinv]"); iIntros "Hlkinv".
  wp_pures.
  wp_bind (For _ _ _).
  wp_apply (wp_forBreak_cond (fun b => wal_linv σₛ.(wal_st) γ ∗ locked #σₛ.(memLock) ∗ logger_inv γ circ_l)%I
              with "[] [$]").
  { iIntros "!>" (Φ') "(Hlkinv&Hlk_held&Hlogger) HΦ".
    wp_apply (wp_load_shutdown with "[$st $Hlkinv]"); iIntros (shutdown) "Hlkinv".
    wp_pures.
    wp_if_destruct.
    - wp_pures.
      wp_apply (wp_Walog__logAppend with "[$Hlkinv $Hlk_held $Hlogger]").
      { iFrame "# ∗". }
      iIntros (progress) "(Hlkinv&Hlk_held&Hlogger)".
      wp_pures.
      wp_if_destruct.
      + wp_loadField.
        wp_apply (wp_condWait with "[$cond_logger $lk $Hlkinv $Hlk_held]").
        iIntros "(Hlk_held&Hlkinv)".
        wp_pures.
        iApply ("HΦ" with "[$]").
      + wp_pures. iApply ("HΦ" with "[$]").
    - iApply ("HΦ" with "[$]").
  }
  iIntros "(Hlkinv&Hlk_held&Hlogger)".
  wp_apply util_proof.wp_DPrintf.
  wp_apply (wp_dec_nthread with "[$st $Hlkinv]"); iIntros "Hlkinv".
  wp_loadField.
  wp_apply (wp_condSignal with "cond_shut").
  wp_loadField.
  wp_apply (release_spec with "[$lk $Hlk_held $Hlkinv]").
  iApply ("HΦ" with "[//]").
Qed.

End goose_lang.
