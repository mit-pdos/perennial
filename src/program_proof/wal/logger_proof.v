From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import auth.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant wal.common_proof.

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
      "HdiskEnd_circ" ∷ diskEnd_linv γ σ.(diskEnd) ∗
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
                               "HdiskEnd_circ" ∷ diskEnd_linv γ σ.(diskEnd) ∗
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
    - iApply "HΦ"; iFrame. iModIntro.
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

Reserved Notation "x ≤ y ≤ z ≤ v ≤ w"
  (at level 70, y at next level, z at next level, v at next level).
Notation "x ≤ y ≤ z ≤ v ≤ w" := (x ≤ y ∧ y ≤ z ∧ z ≤ v ∧ v ≤ w)%nat : nat_scope.

Lemma circ_matches_extend cs txns installed_txn_id installer_pos installer_txn_id diskEnd_mem diskEnd_mem_txn_id diskEnd_txn_id new_txn nextDiskEnd_txn_id :
  (installer_pos ≤ diskEnd_mem ≤ Z.to_nat (circΣ.diskEnd cs))%nat →
  (installed_txn_id ≤ installer_txn_id ≤ diskEnd_mem_txn_id ≤ diskEnd_txn_id ≤ nextDiskEnd_txn_id)%nat →
  (nextDiskEnd_txn_id < length txns)%nat →
  has_updates new_txn (subslice (S diskEnd_txn_id) (S nextDiskEnd_txn_id) txns) →
  circ_matches_txns cs
    txns installed_txn_id installer_pos installer_txn_id diskEnd_mem diskEnd_mem_txn_id diskEnd_txn_id →
  circ_matches_txns (set upds (λ u, u ++ new_txn) cs)
    txns installed_txn_id installer_pos installer_txn_id diskEnd_mem diskEnd_mem_txn_id nextDiskEnd_txn_id.
Proof.
  rewrite /circ_matches_txns /circΣ.diskEnd /=. intuition; last by lia.
  - rewrite -> take_app_le by lia. eauto.
  - rewrite -> subslice_app_1 by lia. eauto.
  - rewrite -> (subslice_split_r (S diskEnd_mem_txn_id) (S diskEnd_txn_id) (S nextDiskEnd_txn_id)) by lia.
    rewrite -> drop_app_le by lia.
    apply has_updates_app; auto.
  - rewrite /circΣ.diskEnd /set /= app_length.
    unfold circΣ.diskEnd in *. lia.
Qed.

Lemma is_installed_extend_durable γ d txns installed_txn_id diskEnd_txn_id diskEnd_txn_id' :
  (diskEnd_txn_id ≤ diskEnd_txn_id' < length txns)%nat →
  is_installed γ d txns installed_txn_id diskEnd_txn_id -∗
  is_installed γ d txns installed_txn_id diskEnd_txn_id'.
Proof.
  intros Hbound.
  iNamed 1.
  iExists _, _. iFrame. iFrame "#".
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
  wp_if_destruct.
  { iApply "HΦ".
    iFrame "Hlocked".
    iSplitR "HnotLogging Happender HownLoggerPos_logger HownLoggerTxn_logger".
    - iExists _; iFrame.
      iExists _; by iFrame "% ∗".
    - by iFrame.
  }
  wp_pures.
  iNamed "HdiskEnd_circ".
  iMod (thread_own_get with "HdiskEnd_exactly HnotLogging") as
      "(HdiskEnd_exactly&Hlog_owned&HareLogging)";
    iNamed "Hlog_owned".
  iNamed "HmemLog_linv".
  iNamed "Hlinv_pers".
  iNamed "HnextDiskEnd".
  iNamed "Hstart_circ".
  iMod (txn_pos_valid_locked with "Hwal HmemStart_txn Howntxns") as "(%HmemStart_txn&Howntxns)".
  iMod (txn_pos_valid_locked with "Hwal HnextDiskEnd_txn Howntxns") as "(%HnextDiskEnd_txn&Howntxns)".
  iMod (get_txns_are _ _ _ _ _ (S installed_txn_id_mem) (S nextDiskEnd_txn_id) with "Howntxns Hwal") as "[Htxns_are Howntxns]"; eauto.
  { pose proof (is_txn_bound _ _ _ HnextDiskEnd_txn).
    lia. }

  (* snapshot the position we're about to write to circular log *)
  iNamed "HownLoggerPos_logger".
  iMod (ghost_var_update_halves σ.(memLog).(slidingM.mutable) with "HownLoggerPos_logger HownLoggerPos_linv") as
        "[HownLoggerPos_logger HownLoggerPos_linv]".
  iNamed "HownLoggerTxn_logger".
  iMod (ghost_var_update_halves nextDiskEnd_txn_id with "HownLoggerTxn_logger HownLoggerTxn_linv") as
        "[HownLoggerTxn_logger HownLoggerTxn_linv]".

  iAssert (ghost_var γ.(txns_name) (1 / 2) txns -∗ |NC={⊤}=> ghost_var γ.(txns_name) (1 / 2) txns ∗ txn_pos γ σ.(locked_diskEnd_txn_id) σ.(diskEnd))%I as "HdiskEnd_pos_helper".
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
    iExists _.
    iSplitL "His_memLog HmemLog HdiskEnd Hshutdown Hnthread".
    1: iExists _; iFrame "∗ # %".
    iSplitL "HdiskEnd_exactly".
    1: iFrame "∗ # %".
    iSplitL "Hstart_exactly".
    1: iFrame "∗ # %".
    iExists _, _, _, _, _, _, _.
    iFrame "HownLoggerPos_linv HownLoggerTxn_linv".
    iFrame.
    iSplitR.
    2: iExists _; iFrame "∗ # %".
    iFrame (HdiskEnd_txn Htxnpos_bound) "#".
    iSplitR.
    1: iPureIntro; lia.
    iSplitR.
    1: iPureIntro; lia.
    iPureIntro.
    intuition.
    2: rewrite ?subslice_zero_length //.
    rewrite -> (subslice_split_r (slidingM.logIndex σ.(memLog) σ.(diskEnd)) (slidingM.logIndex σ.(memLog) logger_pos)) by word.
    rewrite -> (subslice_split_r (S σ.(locked_diskEnd_txn_id)) (S logger_txn_id)); [ | lia | ].
    2: pose proof (is_txn_bound _ _ _ HnextDiskEnd_txn); lia.
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
    iFrame (Hdaddrs_init) "∗ #".
    iSplitL "Hinstalled".
    { iApply (is_installed_extend_durable with "Hinstalled").
      apply is_txn_bound in HnextDiskEnd'.
      apply is_txn_bound in Hend_txn. lia. }
    iSplitL "Hdurable".
    { iNamed "Hdurable".
      iExists _, _, _, _.
      iFrame.
      iPureIntro.
      assert (Hcirc_matches':=Hcirc_matches).
      destruct Hcirc_matches' as (Hmatches_locked_diskEnd&Hmatches_diskEnd_mem&Hmatches_diskEnd&Hcirc_log_index_ordering&Hcirc_txn_id_ordering).
      apply (circ_matches_extend _ _ _ _ _ _ _ diskEnd_txn_id); eauto; try lia.
      { apply is_txn_bound in HnextDiskEnd'.
        apply is_txn_bound in Hend_txn. lia. }
      pose proof (is_txn_bound _ _ _ HnextDiskEnd_txn).
      rewrite -> subslice_length in Htxns_are by lia.
      replace (S installed_txn_id_mem + (S nextDiskEnd_txn_id - S installed_txn_id_mem))%nat
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
  iNamed "HmemLog_linv".
  iDestruct (ghost_var_agree with "HownLoggerPos_linv HownLoggerPos_logger") as %Heqloggerpos; subst.
  iDestruct (ghost_var_agree with "HownLoggerTxn_linv HownLoggerTxn_logger") as %Heqloggertxn; subst.

  iAssert (ghost_var γ.(txns_name) (1 / 2) txns0 -∗ |NC={⊤}=>
           ghost_var γ.(txns_name) (1 / 2) txns0 ∗
           ⌜is_txn txns0 nextDiskEnd_txn_id σ.(memLog).(slidingM.mutable)⌝ ∗
           ⌜subslice (S installed_txn_id_mem) (S nextDiskEnd_txn_id) txns0 =
            subslice (S installed_txn_id_mem) (S nextDiskEnd_txn_id) txns⌝)%I
    as "Htxns0_helper".
  {
    iIntros "Howntxns".
    iInv "Hwal" as (σs) "[Hinner HP]".
    iDestruct "Hinner" as "(>%Hwf&Hmem&>?&>?&>?&>?)"; iNamed.
    iDestruct (ghost_var_agree with "Howntxns γtxns") as %->.
    iFrame "Howntxns".
    iDestruct (txn_pos_valid_general with "Htxns_ctx HnextDiskEnd_txn_old") as %H.
    iDestruct (txns_are_sound with "Htxns_ctx Htxns_are") as %Htxns.
    replace ((S installed_txn_id_mem) + length (subslice (S installed_txn_id_mem) (S nextDiskEnd_txn_id) txns))%nat with (S nextDiskEnd_txn_id) in Htxns.
    2: {
      rewrite subslice_length; try lia.
      pose proof (is_txn_bound _ _ _ HnextDiskEnd_txn). lia.
    }
    iModIntro. iSplitL; last by done. iModIntro. iExists _. iFrame. iFrame "%".
  }
  iMod ("Htxns0_helper" with "Howntxns") as "(Howntxns & %HnextDiskEnd_txns0 & %Htxns)".

  iDestruct (updates_slice_frag_len with "Hupds") as "%Hupds_len".
  rewrite subslice_length in Hupds_len; last by word.
  rewrite logIndex_diff in Hupds_len; last by word.

  replace (int.Z σ.(diskEnd) +
      (slidingM.logIndex σ.(memLog) σ.(memLog).(slidingM.mutable) -
      slidingM.logIndex σ.(memLog) σ.(diskEnd))%nat)
    with (int.Z σ.(memLog).(slidingM.mutable))
    by (rewrite logIndex_diff; word).
  wp_seq.
  wp_bind Skip.
  iInv "Hwal" as (σs) "[Hinner HP]".
  iApply wp_ncfupd.
  wp_call.

  iAssert (
    "Hinner" ∷ is_wal_inner l γ σs dinit -∗
    "Howntxns" ∷ ghost_var γ.(txns_name) (1/2) txns0 -∗
    "HdiskEnd_is" ∷ diskEnd_is γ.(circ_name) (1/2) (int.Z σ.(memLog).(slidingM.mutable)) -∗
    "HownDiskEndMem_linv" ∷ mono_nat_auth_own γ.(diskEnd_mem_name) (1/2) (int.nat σ0.(diskEnd)) -∗
    "HownDiskEndMemTxn_linv" ∷ mono_nat_auth_own γ.(diskEnd_mem_txn_id_name) (1/2) σ0.(locked_diskEnd_txn_id) -∗
    |NC={⊤ ∖ ↑walN.@"wal"}=>
    "Hinner" ∷ is_wal_inner l γ σs dinit ∗
    "Howntxns" ∷ ghost_var γ.(txns_name) (1/2) txns0 ∗
    "HdiskEnd_is" ∷ diskEnd_is γ.(circ_name) (1/2) (int.Z σ.(memLog).(slidingM.mutable)) ∗
    "HownDiskEndMem_linv" ∷ mono_nat_auth_own γ.(diskEnd_mem_name) (1/2) (int.nat (int.Z σ.(diskEnd) + int.Z s.(Slice.sz))) ∗
    "HownDiskEndMemTxn_linv" ∷ mono_nat_auth_own γ.(diskEnd_mem_txn_id_name) (1/2) nextDiskEnd_txn_id
  )%I as "HdiskEndMem_update".
  {
    iIntros; iNamed.
    iDestruct "Hinner" as "(%Hwf&Hmem&?&?&?&?)"; iNamed.
    iNamed "Hdisk".
    iNamed "Hdisk".
    iNamed "Hdurable".
    iDestruct "circ.end" as (diskEnd_disk) "circ.end".
    iNamed "circ.end".
    iNamed "Hlinv_pers".
    rewrite Hupds_len.
    replace (int.nat (int.Z σ.(diskEnd) +
      (int.nat σ.(memLog).(slidingM.mutable) - int.nat σ.(diskEnd))%nat))
      with (int.nat σ.(memLog).(slidingM.mutable))%nat by word.
    iDestruct (mono_nat_auth_own_agree with "HownDiskEndMem_walinv HownDiskEndMem_linv") as %[_ ->].
    iDestruct (mono_nat_auth_own_agree with "HownDiskEndMemTxn_walinv HownDiskEndMemTxn_linv") as %[_ ->].
    iMod (mono_nat_own_update_halves (int.nat σ.(memLog).(slidingM.mutable))
      with "HownDiskEndMem_walinv HownDiskEndMem_linv")
      as "(HownDiskEndMem_walinv&HownDiskEndMem_linv&_)".
    1: lia.
    iMod (mono_nat_own_update_halves nextDiskEnd_txn_id
      with "HownDiskEndMemTxn_walinv HownDiskEndMemTxn_linv")
      as "(HownDiskEndMemTxn_walinv&HownDiskEndMemTxn_linv&_)".
    1: lia.
    iDestruct (ghost_var_agree with "Howntxns γtxns") as %->.
    iMod (is_circular_diskEnd_is_agree
      with "HdiskEnd_is Hcirc Howncs")
      as "(%Hmutable_eq&HdiskEnd_is&Howncs)".
    1: solve_ndisj.
    rewrite -Hmutable_eq in HdiskEnd_val.
    apply (inj int.Z) in HdiskEnd_val.
    subst diskEnd_disk.
    iDestruct (subslice_stable_nils2 _ _ nextDiskEnd_txn_id diskEnd_txn_id _ Hwf with "[HnextDiskEnd_inv HnextDiskEnd_stable_old]") as %Hnils; eauto.
    iDestruct (subslice_stable_nils2 _ _ diskEnd_txn_id nextDiskEnd_txn_id _ Hwf with "[HnextDiskEnd_inv Hend_txn_stable]") as %Hnils2; eauto.

    (* this is mostly the same proof as the one for wp_apply wp_circular__Append...
      could this be made into a lemma? *)
    iModIntro.
    iSplitR "HownDiskEndMem_linv HownDiskEndMemTxn_linv Howntxns HdiskEnd_is".
    2: iFrame; done.
    iFrame (Hwf) "∗".
    iExists _.
    iFrame "Howncs".
    iExists installed_txn_id, (Nat.max diskEnd_txn_id nextDiskEnd_txn_id).
    iFrame (Hdaddrs_init) "∗ #".
    iSplitL "Hinstalled".
    { iApply (is_installed_extend_durable with "Hinstalled").
      apply is_txn_bound in HnextDiskEnd_txns0.
      apply is_txn_bound in Hend_txn. lia. }
    iSplitL.
    2: {
      iExists σ.(memLog).(slidingM.mutable).
      iSplit.
      { iPureIntro.
        lia. }
      iFrame (Hmutable_eq).
      destruct (decide (diskEnd_txn_id ≤ nextDiskEnd_txn_id)).
      { rewrite max_r; last by lia. iFrame "HnextDiskEnd_stable_old". iPureIntro; eauto. }
      rewrite max_l; last by lia.
      iFrame (Hend_txn) "Hend_txn_stable".
    }
    iExists _, _, _, _.
    iFrame.
    iPureIntro.
    assert (Hcirc_matches':=Hcirc_matches).
    destruct Hcirc_matches' as (Hmatches_locked_diskEnd&Hmatches_diskEnd_mem&Hmatches_diskEnd&Hcirc_log_index_ordering&Hcirc_txn_id_ordering).
    rewrite /circ_matches_txns.
    rewrite /circΣ.diskEnd in Hcirc_log_index_ordering.
    intuition try lia.
    - rewrite Hmutable_eq /circΣ.diskEnd.
      replace (Z.to_nat (int.Z (start cs) + length (upds cs)) - int.nat (start cs))%nat
        with (length (upds cs)) by word.
      apply (has_updates_app _ _ _ _ Hmatches_diskEnd_mem) in Hmatches_diskEnd.
      rewrite subslice_app_contig in Hmatches_diskEnd; last by lia.
      rewrite -(subslice_to_end _ (length cs.(upds))) in Hmatches_diskEnd; last by lia.
      rewrite subslice_app_contig in Hmatches_diskEnd; last by lia.
      destruct (decide (diskEnd_txn_id ≤ nextDiskEnd_txn_id)).
      {
        assert (has_updates [] (subslice (S diskEnd_txn_id) (S nextDiskEnd_txn_id) σs.(log_state.txns))) as Hmatches_tail.
        {
          rewrite -(app_nil_r (subslice _ _ _)).
          apply (has_updates_prepend_nils_2 _ _ _ Hnils2).
          apply has_updates_nil.
        }
        apply (has_updates_app _ _ _ _ Hmatches_diskEnd) in Hmatches_tail.
        rewrite app_nil_r subslice_app_contig in Hmatches_tail.
        2: lia.
        apply Hmatches_tail.
      }
      apply (has_updates_app_nils_2 _ _ _ Hnils).
      rewrite subslice_app_contig; last by lia.
      apply Hmatches_diskEnd.
    - rewrite Hmutable_eq /circΣ.diskEnd.
      replace (Z.to_nat (int.Z (start cs) + length (upds cs)) - int.nat (start cs))%nat
        with (length (upds cs)) by word.
      rewrite drop_all.
      destruct (decide (diskEnd_txn_id ≤ nextDiskEnd_txn_id)).
      {
        rewrite max_r; last by lia.
        rewrite subslice_zero_length.
        apply has_updates_nil.
      }
      rewrite max_l; last by lia.
      rewrite -(app_nil_r (subslice _ _ _)).
      apply (has_updates_prepend_nils_2 _ _ _ Hnils).
      apply has_updates_nil.
  }
  iMod ("HdiskEndMem_update"
    with "Hinner Howntxns HdiskEnd_is HownDiskEndMem_linv HownDiskEndMemTxn_linv")
    as "Hupdate_post".
  iNamed "Hupdate_post".
  iModIntro.
  iModIntro.
  iSplitL "Hinner Hcirc HP".
  1: iExists _; iFrame.

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
    simpl.
    iSplitL "HmemLog HdiskEnd Hshutdown Hnthread His_memLog".
    {
      iExists _.
      iFrame.
      iNamed "Hlinv_pers".
      iPureIntro.
      rewrite Hupds_len.
      unfold locked_wf in *. simpl.
      split; [|intuition; lia].
      split; word.
    }
    iFrame "Hstart_circ".
    iSplitL "HdiskEnd_exactly".
    {
      rewrite Hupds_len.
      replace (int.Z σ.(diskEnd) +
           (int.nat σ.(memLog).(slidingM.mutable) - int.nat σ.(diskEnd))%nat)
        with (int.Z σ.(memLog).(slidingM.mutable)) by word.
      replace (U64 (int.Z σ.(memLog).(slidingM.mutable))) with σ.(memLog).(slidingM.mutable) by word.
      by iFrame "∗ #".
    }

    iExists _, nextDiskEnd_txn_id0, _, _, _, _, _.
    iFrame. iModIntro.
    iClear "HinstalledTxn_lb".
    iNamed "Hlinv_pers".
    iNamed "Htxns".
    iFrame "HmemStart_txn HmemEnd_txn".
    iFrame "HnextDiskEnd_stable_old".
    iFrame "HinstalledTxn_lb".

    iSplit.
    { iPureIntro. word. }
    iSplit.
    { iPureIntro. lia. }
    iSplit.
    { rewrite Hupds_len.
      replace (U64 (int.Z σ.(diskEnd) + (int.nat σ.(memLog).(slidingM.mutable) - int.nat σ.(diskEnd))%nat))
        with (σ.(memLog).(slidingM.mutable)) by word.
      done.
    }
    iSplit.
    2: done.
    rewrite /memLog_linv_txns.
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
    pose proof (has_updates_app _ _ _ _ His_diskEnd0 His_loggerEnd0) as His_memStart_new.

    rewrite (subslice_split_r (S installer_txn_id_mem0) (S σ0.(locked_diskEnd_txn_id)) (S nextDiskEnd_txn_id) txns0); try lia.
    rewrite Hupds_len.
    replace (int.Z σ.(diskEnd) +
         (int.nat σ.(memLog).(slidingM.mutable) - int.nat σ.(diskEnd))%nat : u64)
      with (σ.(memLog).(slidingM.mutable)) by word.

    rewrite (subslice_split_r (slidingM.logIndex σ0.(memLog) installer_pos_mem0)
                (slidingM.logIndex σ0.(memLog) σ0.(diskEnd))
                (slidingM.logIndex σ0.(memLog) σ.(memLog).(slidingM.mutable)) σ0.(memLog).(slidingM.log)); try word.
    iPureIntro.
    eauto.
  - iFrame.
    iSplitL "HownLoggerPos_logger".
    + iExists _; by iFrame.
    + iExists _; by iFrame.
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
  by iApply ("HΦ" with "[//]").
Qed.

End goose_lang.
