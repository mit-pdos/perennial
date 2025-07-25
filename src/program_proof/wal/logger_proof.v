From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import auth.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant wal.common_proof.

Section goose_lang.
Context `{!heapGS Σ}.
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
  {{{ "#HmemLock" ∷ readonly (l ↦[Walog :: "memLock"] #σₛ.(memLock)) ∗
      "#HcondLogger" ∷ readonly (l ↦[Walog :: "condLogger"] #σₛ.(condLogger)) ∗
      "#HcondInstall" ∷ readonly (l ↦[Walog :: "condInstall"] #σₛ.(condInstall)) ∗
      "#His_cond1" ∷ is_cond σₛ.(condLogger) #σₛ.(memLock) ∗
      "#His_cond2" ∷ is_cond σₛ.(condInstall) #σₛ.(memLock) ∗
      "#?" ∷ readonly (l ↦[Walog :: "st"] #σₛ.(wal_st)) ∗
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
  wp_rec. wp_pures.
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
    iPureIntro. inversion 1.
  }
  { iIntros "!>" (Φ') "HI HΦ".
    iNamed "HI".
    iNamed "Hfields".
    iNamed "Hfield_ptsto".
    wp_loadField. wp_loadField.
    wp_apply (wp_log_len with "His_memLog"); iIntros "His_memLog".
    wp_pures.
    change (uint.Z (word.divu (word.sub 4096 8) 8)) with LogSz.
    wp_if_destruct.
    - wp_loadField.
      wp_apply (wp_Cond__Wait with "[-HΦ]"); [ iFrame "His_cond2 His_lock Hlocked" | ].
      { by iFrame "∗ #". }
      iIntros "(Hlocked&Hlkinv)".
      wp_pures.
      iApply "HΦ"; iFrame.
      iNamed "Hlkinv".
      iExists _; iFrame "∗#".
      iPureIntro; inversion 1.
    - iApply "HΦ"; iFrame.
      iPureIntro. split; [done | ].
      intros _.
      unfold locked_wf, slidingM.wf in Hlocked_wf.
      revert Heqb; word.
  }
  iIntros "HI"; iNamed "HI".
  specialize (Hbreak ltac:(auto)).
  wp_pures. iModIntro. iApply "HΦ".
  iFrameNamed. auto.
Qed.

Hint Unfold slidingM.logIndex slidingM.wf : word.

Reserved Notation "x ≤ y ≤ z ≤ v ≤ w"
  (at level 70, y at next level, z at next level, v at next level).
Notation "x ≤ y ≤ z ≤ v ≤ w" := (x ≤ y ∧ y ≤ z ∧ z ≤ v ∧ v ≤ w)%nat : nat_scope.

Lemma circ_matches_extend cs txns installed_txn_id installer_pos installer_txn_id diskEnd_mem diskEnd_mem_txn_id diskEnd_txn_id new_txn nextDiskEnd_txn_id :
  (diskEnd_txn_id ≤ nextDiskEnd_txn_id < length txns)%nat →
  is_memLog_region (subslice (S diskEnd_txn_id) (S nextDiskEnd_txn_id) txns) new_txn →
  circ_matches_txns cs
    txns installed_txn_id installer_pos installer_txn_id diskEnd_mem diskEnd_mem_txn_id diskEnd_txn_id →
  circ_matches_txns (set upds (λ u, u ++ new_txn) cs)
    txns installed_txn_id installer_pos installer_txn_id diskEnd_mem diskEnd_mem_txn_id nextDiskEnd_txn_id.
Proof.
  rewrite /circ_matches_txns /circΣ.diskEnd /=.
  intros Hbnd Hhas Hbndrys.
  split.
  {
    rewrite length_app.
    intros bndry Hbndry.
    apply list_elem_of_lookup in Hbndry.
    destruct Hbndry as [i Hbndry].
    destruct Hbndrys as [Hbnds _].
    specialize (Hbnds bndry).
    do 3 (destruct i; first by (
      simpl in Hbndry; inversion Hbndry; subst bndry; simpl; simpl in Hbnds;
      (unshelve (epose proof (Hbnds _)); first by set_solver); lia
    )).
    destruct i; last by inversion Hbndry.
    simpl in Hbndry.
    inversion Hbndry.
    subst bndry.
    simpl.
    lia.
  }
  pose proof Hbndrys as [Hbnds Hreg].
  intros i bndry1 bndry2 Hbndry1 Hbndry2.
  specialize (Hreg i bndry1 bndry2).
  specialize (Hbnds bndry2).
  do 2 (destruct i; first by (
    simpl in Hbndry1; inversion Hbndry1; subst bndry1; clear Hbndry1;
    simpl in Hbndry2; inversion Hbndry2; subst bndry2; clear Hbndry2;
    (unshelve (epose proof (Hreg _ _) as Hreg'); try reflexivity);
    (unshelve (epose proof (Hbnds _) as Hbnds'); first by set_solver);
    simpl in Hreg'; simpl in Hbnds'; simpl;
    (rewrite subslice_app_1; last by lia);
    assumption
  )).
  destruct i; last by inversion Hbndry2.
  clear Hbnds Hreg.
  pose proof Hbndrys as [Hbnds Hreg].
  specialize (Hbnds bndry1).
  simpl in Hbndry1; inversion Hbndry1; subst bndry1; clear Hbndry1;
  simpl in Hbndry2; inversion Hbndry2; subst bndry2; clear Hbndry2.
  simpl.
  unshelve (epose proof (Hbnds _) as Hbnds'); first by set_solver.
  simpl in Hbnds'.
  unshelve (epose proof (Hreg mwrb_de _ _ _ _) as Hreg').
  3-4: reflexivity.
  simpl in Hreg'.
  rewrite -subslice_from_drop length_app.
  split; first by lia.
  split; first by lia.
  rewrite drop_app_le; last by lia.
  rewrite -subslice_from_drop in Hreg'.
  destruct Hreg' as (Hbndu&Hbndt&Hreg').
  erewrite <- subslice_app_contig.
  1: apply is_memLog_region_app; eassumption.
  lia.
Qed.

Lemma is_installed_extend_durable γ d txns installed_txn_id installer_txn_id diskEnd_txn_id diskEnd_txn_id' :
  (diskEnd_txn_id ≤ diskEnd_txn_id' < length txns)%nat →
  is_installed γ d txns installed_txn_id installer_txn_id diskEnd_txn_id -∗
  is_installed γ d txns installed_txn_id installer_txn_id diskEnd_txn_id'.
Proof.
  intros Hbound.
  iNamed 1.
  iExists _. iFrame. iFrame "#".
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
  uint.Z memLog.(slidingM.start) ≤ uint.Z pos1 →
  (slidingM.logIndex memLog pos2 - slidingM.logIndex memLog pos1)%nat =
  (uint.nat pos2 - uint.nat pos1)%nat.
Proof.
  rewrite /slidingM.logIndex; intros.
  lia.
Qed.

Theorem wp_Walog__flushIfNeeded l γ dinit σₛ σ :
  {{{
      "#?" ∷ readonly (l ↦[Walog :: "st"] #σₛ.(wal_st)) ∗
      "#Hwal" ∷ is_wal P l γ dinit ∗
      "Hlkinv" ∷ wal_linv_core σₛ.(wal_st) γ σ
  }}}
    Walog__flushIfNeeded #l
  {{{ σ', RET #();
      wal_linv_core σₛ.(wal_st) γ σ' ∗
      ⌜length σ.(memLog).(slidingM.log) = length σ'.(memLog).(slidingM.log)⌝
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ"; iNamed "Hpre".
  wp_rec. wp_pures.
  iNamed "Hlkinv". iNamed "Hfields". iNamed "Hfield_ptsto".
  iNamed "His_memLog". iNamed "Hinv". iNamed "needFlush".
  wp_loadField. wp_loadField. wp_loadField.
  wp_if_destruct.
  2: {
    iApply "HΦ".
    iModIntro.
    iSplitL; last by trivial.
    by iFrame "∗#".
  }
  wp_loadField.
  wp_apply (wp_sliding__clearMutable_wal with "[
    $Hwal
    HmemLog HdiskEnd Hshutdown Hnthread
    log start mutable addrPos needFlush
    log_mutable is_addrPos
    HdiskEnd_circ Hstart_circ HmemLog_linv
  ]").
  { by iFrame "∗#". }
  clear.
  iIntros (σ') "[Hlkinv %HmemLog_len]".
  iNamed "Hlkinv". iNamed "Hfields". iNamed "Hfield_ptsto".
  iNamed "His_memLog". iNamed "Hinv".
  iRename "log_readonly" into "log_readonl0".
  iNamed "Hinv". iNamed "needFlush".
  wp_loadField. wp_loadField. wp_storeField.
  iApply "HΦ".
  iModIntro.
  iFrame (HmemLog_len).
  iFrame "∗%#".
Qed.

Theorem wp_Walog__logAppend l circ_l γ dinit σₛ :
  {{{ "#HmemLock" ∷ readonly (l ↦[Walog :: "memLock"] #σₛ.(memLock)) ∗
      "#HcondLogger" ∷ readonly (l ↦[Walog :: "condLogger"] #σₛ.(condLogger)) ∗
      "#HcondInstall" ∷ readonly (l ↦[Walog :: "condInstall"] #σₛ.(condInstall)) ∗
      "#d" ∷ readonly (l ↦[Walog :: "d"] σₛ.(wal_d)) ∗
      "#circ" ∷ readonly (l ↦[Walog :: "circ"] #σₛ.(circ)) ∗
      "#His_cond1" ∷ is_cond σₛ.(condLogger) #σₛ.(memLock) ∗
      "#His_cond2" ∷ is_cond σₛ.(condInstall) #σₛ.(memLock) ∗
      "#?" ∷ readonly (l ↦[Walog :: "st"] #σₛ.(wal_st)) ∗
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
  wp_rec. wp_pures.
  wp_apply (wp_Walog__waitForSpace with "[$Hlkinv $Hlocked]").
  { iFrameNamed. iFrame "#". }
  iIntros (σ) "Hpost"; iNamed "Hpost".

  wp_apply (wp_Walog__flushIfNeeded with "[
    $Hwal
    Hfields HdiskEnd_circ Hstart_circ HmemLog_linv
  ]").
  { iSplit; first by iFrame "#". iFrame. }
  iIntros (σ') "[Hlkinv %HmemLog_len]".
  rewrite HmemLog_len in Hhas_space.
  clear HmemLog_len σ. rename σ' into σ.

  iNamed "Hlkinv".
  iNamed "Hlogger".
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
    iSplitR "
      HnotLogging Happender
      HownLoggerPos_logger HownLoggerTxn_logger
      HownDiskEndMem_logger HownDiskEndMemTxn_logger
      HownDiskEnd_logger HownDiskEndTxn_logger
    ".
    - by iFrame.
    - iExists _, _. by iFrame.
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
  iDestruct (ghost_var_agree with
    "HownLoggerPos_logger HownLoggerPos_linv"
  ) as %<-.
  iDestruct (ghost_var_agree with
    "HownLoggerTxn_logger HownLoggerTxn_linv"
  ) as %<-.
  iDestruct (mono_nat_auth_own_agree with
    "HownDiskEndMem_logger HownDiskEndMem_linv"
  ) as %[_ HoldDiskEnd_eq].
  iDestruct (mono_nat_auth_own_agree with
    "HownDiskEndMemTxn_logger HownDiskEndMemTxn_linv"
  ) as %[_ ->].
  iMod (ghost_var_update_halves σ.(memLog).(slidingM.mutable) with
    "HownLoggerPos_logger HownLoggerPos_linv"
  ) as "[HownLoggerPos_logger HownLoggerPos_linv]".
  iMod (ghost_var_update_halves nextDiskEnd_txn_id with
    "HownLoggerTxn_logger HownLoggerTxn_linv"
  ) as "[HownLoggerTxn_logger HownLoggerTxn_linv]".
  rename diskEnd into oldDiskEnd.
  apply Z2Nat.inj in HoldDiskEnd_eq.
  2-3: word.
  apply word.unsigned_inj in HoldDiskEnd_eq.
  subst oldDiskEnd.

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
    iFrame "HdiskEnd_pos Howntxns γtxns".
    iSplitL; try done.
    iModIntro. iFrame "∗%".
  }
  iMod ("HdiskEnd_pos_helper" with "Howntxns") as "[Howntxns #HdiskEnd_pos]".

  (* use this to also strip a later, which the [wp_loadField] tactic does not do *)
  wp_apply (wp_loadField_ro with "HmemLock").
  iDestruct "Htxns_are" as "#Htxns_are".
  wp_apply (wp_Mutex__Unlock with "[
    -HΦ HareLogging HdiskEnd_is Happender Hbufs $His_lock $Hlocked
    HownLoggerPos_logger HownLoggerTxn_logger
    HownDiskEndMem_logger HownDiskEndMemTxn_logger
    HownDiskEnd_logger HownDiskEndTxn_logger
  ]").
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
    2: iFrame "∗ # %".
    iFrame (HdiskEnd_txn Htxnpos_bound) "#".
    iPureIntro.
    split; first by lia.
    split; first by lia.
    split; last by lia.
    eapply (is_memLog_boundaries_move _ _ _ mwrb_uss) in Htxns;
      last by reflexivity.
    assumption.
  }
  wp_loadField.
  iDestruct "Hwal" as "[Hwal Hcirc]".

  wp_apply (
    wp_circular__Append _ _ (
        "HownDiskEndMem_logger" ∷ mono_nat_auth_own γ.(diskEnd_mem_name) (1/2) (_: nat) ∗
        "HownDiskEndMemTxn_logger" ∷ mono_nat_auth_own γ.(diskEnd_mem_txn_id_name) (1/2) (_: nat) ∗
        "HownDiskEnd_logger" ∷ ghost_var γ.(diskEnd_name) (1/2) (_: nat) ∗
        "HownDiskEndTxn_logger" ∷ ghost_var γ.(diskEnd_txn_id_name) (1/2) (_: nat)
    ) with "[
      $Hbufs $HdiskEnd_is $Happender $Hcirc $Hstart_at_least
      HownDiskEnd_logger HownDiskEndTxn_logger
      HownDiskEndMem_logger HownDiskEndMemTxn_logger
    ]"
  ).
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
    iMod (ghost_var_update_halves with "Hcirc_ctx Howncs") as "[Hcirc_ctx Howncs]".

    iDestruct (txn_pos_valid_general with "Htxns_ctx HdiskEnd_pos") as %HdiskEnd_pos.
    iNamed "circ.end".

    rewrite HdiskEnd_eq in HdiskEnd_val.
    assert (diskEnd = σ.(invariant.diskEnd)) by word; subst.
    iDestruct (subslice_stable_nils2 with "[$HnextDiskEnd_inv $HdiskEnd_stable]") as "%HdiskEnd_nils_1";
      [ eauto | apply HdiskEnd_pos | apply Hend_txn | ].
    iDestruct (subslice_stable_nils2 with "[$HnextDiskEnd_inv $Hend_txn_stable]") as "%HdiskEnd_nils_2";
      [ eauto | apply Hend_txn | apply HdiskEnd_pos | ].

    iNamed "Hdurable".
    iDestruct (mono_nat_auth_own_agree with
      "HownDiskEndMem_logger HownDiskEndMem_walinv"
    ) as %[_ <-].
    iDestruct (mono_nat_auth_own_agree with
      "HownDiskEndMemTxn_logger HownDiskEndMemTxn_walinv"
    ) as %[_ <-].
    iDestruct (ghost_var_agree with
      "HownDiskEnd_logger HownDiskEnd_walinv"
    ) as %Heq_diskEnd.
    iDestruct (ghost_var_agree with
      "HownDiskEndTxn_logger HownDiskEndTxn_walinv"
    ) as %<-.
    iMod (ghost_var_update_halves (_: nat) with
      "HownDiskEnd_logger HownDiskEnd_walinv"
    ) as "[HownDiskEnd_logger HownDiskEnd_walinv]".
    iMod (ghost_var_update_halves (_: nat) with
      "HownDiskEndTxn_logger HownDiskEndTxn_walinv"
    ) as "[HownDiskEndTxn_logger HownDiskEndTxn_walinv]".
    pose proof (circ_matches_txns_bounds _ _ _ _ _ _ _ _ Hcirc_matches)
      as Hbounds.

    iModIntro.
    iSplitR "
      HownDiskEndMem_logger HownDiskEndMemTxn_logger
      HownDiskEnd_logger HownDiskEndTxn_logger
      Hcirc_ctx
    "; last by iFrame.
    iNext.
    iFrame "HP Howncs Hmem Htxns_ctx γtxns HnextDiskEnd_inv".
    iSplitR; auto.
    iExists installed_txn_id, installer_txn_id, nextDiskEnd_txn_id.
    iSplitL "Hinstalled".
    { iApply (is_installed_extend_durable with "Hinstalled").
      apply is_txn_bound in HnextDiskEnd'.
      apply is_txn_bound in Hend_txn. lia. }
    iFrame (Hdaddrs_init) "#".
    iSplitL.
    {
      iExists _, _, _.
      iFrame.
      rewrite /circΣ.diskEnd in HdiskEnd_eq.
      rewrite /circΣ.diskEnd /slidingM.logIndex /=
        length_app subslice_length;
        last by word.
      replace (uint.nat (uint.Z _ + ( _ + _ )%nat)) with
        (uint.nat σ.(memLog).(slidingM.mutable)) by word.
      iFrame.

      iPureIntro.
      pose proof (is_txn_bound _ _ _ HnextDiskEnd').
      pose proof (is_txn_bound _ _ _ HnextDiskEnd_txn).
      rewrite -> subslice_length in Htxns_are by lia.
      replace (S installed_txn_id_mem + (S nextDiskEnd_txn_id - S installed_txn_id_mem))%nat
              with (S nextDiskEnd_txn_id) in Htxns_are by lia.
      apply (subslice_suffix_eq _ _ _ (S σ.(locked_diskEnd_txn_id))) in Htxns_are; last by lia.

      split; last by word.

      apply circ_matches_extend
        with (diskEnd_txn_id := σ.(locked_diskEnd_txn_id));
        last by assumption.
      1: lia.

      unshelve (epose proof (
        is_memLog_boundaries_region mwrb_de mwrb_us _ _ _ _ _ _ Htxns _ _
      ) as Hreg).
      3: rewrite /mwrb_de /mwrb_us; lia.
      3-4: reflexivity.
      simpl in Hreg.
      destruct Hreg as (Hbndu&Hbndt&Hreg).


      rewrite -Htxns_are in Hreg.
      assumption.
    }
    iExists σ.(memLog).(slidingM.mutable).
    iExists durable_lb_alt.
    iSplit; first by (iPureIntro; lia).
    iSplit; first by (iPureIntro; lia).
    iSplit; first by (iPureIntro; assumption).
    iSplit.
    {
      iPureIntro.
      destruct (decide (nextDiskEnd_txn_id ≤ σs.(log_state.durable_lb))%nat)
        as [Hcmp|Hcmp].
      2: {
        rewrite Nat.max_r; last by lia.
        assumption.
      }
      rewrite Nat.max_l; last by lia.
      destruct (decide (
        σ.(locked_diskEnd_txn_id) ≤ σs.(log_state.durable_lb))%nat
      ); last by lia.
      rewrite Nat.max_l in Hdurable_lb_pos; last by lia.
      pose proof (wal_wf_txns_mono_pos'
        Hwf HnextDiskEnd' Hdurable_lb_pos Hcmp).
      assert (uint.Z σ.(memLog).(slidingM.mutable) = uint.Z σ.(diskEnd))
        as Hmutable_diskEnd by lia.
      apply word.unsigned_inj in Hmutable_diskEnd.
      rewrite Hmutable_diskEnd.
      assumption.
    }
    iSplit.
    { iPureIntro.
      simpl.
      rewrite circ_diskEnd_app.
      rewrite -> subslice_length by word.
      rewrite -> logIndex_diff by word.
      word. }
    iSplit; first by (iPureIntro; assumption).
    destruct (decide (σs.(log_state.durable_lb) ≤ nextDiskEnd_txn_id)%nat).
    {
      rewrite (Nat.max_r _ nextDiskEnd_txn_id); last by lia.
      iFrame "#".
    }
    rewrite (Nat.max_l _ nextDiskEnd_txn_id); last by lia.
    destruct (decide
      (σs.(log_state.durable_lb) ≤ σ.(locked_diskEnd_txn_id))%nat
    ); first by lia.
    rewrite Nat.max_l; last by lia.
    iFrame "#".
  }

  rewrite -> subslice_length by word.
  iIntros "(Hpost&Hupds&Hcirc_appender&HdiskEnd_is)"; iNamed "Hpost".
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "His_lock").
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

  rename Htxns into Htxns_old.
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
    iModIntro. by iFrame "∗%".
  }
  iMod ("Htxns0_helper" with "Howntxns") as "(Howntxns & %HnextDiskEnd_txns0 & %Htxns)".

  iDestruct (updates_slice_frag_len with "Hupds") as "%Hupds_len".
  rewrite subslice_length in Hupds_len; last by word.
  rewrite logIndex_diff in Hupds_len; last by word.

  replace (uint.Z σ.(diskEnd) +
      (slidingM.logIndex σ.(memLog) σ.(memLog).(slidingM.mutable) -
      slidingM.logIndex σ.(memLog) σ.(diskEnd))%nat)
    with (uint.Z σ.(memLog).(slidingM.mutable))
    by (rewrite logIndex_diff; word).
  do 2 wp_pure.
  wp_bind Skip.
  iInv "Hwal" as (σs) "[Hinner HP]".
  iApply wp_ncfupd.
  wp_rec. wp_pures.

  iDestruct (mono_nat_auth_own_agree with
    "HownDiskEndMem_logger HownDiskEndMem_linv"
  ) as %[_ Heq_diskEndMem].
  iDestruct (mono_nat_auth_own_agree with
    "HownDiskEndMemTxn_logger HownDiskEndMemTxn_linv"
  ) as %[_ Heq_diskEndMemTxn].
  rewrite -Heq_diskEndMem -Heq_diskEndMemTxn.

  iAssert (∀ diskEnd diskEnd_txn_id nextDiskEnd nextDiskEnd_txn_id,
    "%Hmono" ∷ ⌜diskEnd ≤ nextDiskEnd⌝%nat -∗
    "Hinner" ∷ is_wal_inner l γ σs dinit -∗
    "HownDiskEndMem_linv" ∷ mono_nat_auth_own γ.(diskEnd_mem_name) (1/2/2) diskEnd -∗
    "HownDiskEndMemTxn_linv" ∷ mono_nat_auth_own γ.(diskEnd_mem_txn_id_name) (1/2/2) diskEnd_txn_id -∗
    "HownDiskEndMem_logger" ∷ mono_nat_auth_own γ.(diskEnd_mem_name) (1/2) diskEnd -∗
    "HownDiskEndMemTxn_logger" ∷ mono_nat_auth_own γ.(diskEnd_mem_txn_id_name) (1/2) diskEnd_txn_id -∗
    "HownDiskEnd_logger" ∷ ghost_var γ.(diskEnd_name) (1/2) nextDiskEnd -∗
    "HownDiskEndTxn_logger" ∷ ghost_var γ.(diskEnd_txn_id_name) (1/2) nextDiskEnd_txn_id -∗
    |NC={⊤ ∖ ↑walN.@"wal"}=>
    "Hinner" ∷ is_wal_inner l γ σs dinit ∗
    "HownDiskEndMem_linv" ∷ mono_nat_auth_own γ.(diskEnd_mem_name) (1/2/2) nextDiskEnd ∗
    "HownDiskEndMemTxn_linv" ∷ mono_nat_auth_own γ.(diskEnd_mem_txn_id_name) (1/2/2) nextDiskEnd_txn_id ∗
    "HownDiskEndMem_logger" ∷ mono_nat_auth_own γ.(diskEnd_mem_name) (1/2) nextDiskEnd ∗
    "HownDiskEndMemTxn_logger" ∷ mono_nat_auth_own γ.(diskEnd_mem_txn_id_name) (1/2) nextDiskEnd_txn_id ∗
    "HownDiskEnd_logger" ∷ ghost_var γ.(diskEnd_name) (1/2) nextDiskEnd ∗
    "HownDiskEndTxn_logger" ∷ ghost_var γ.(diskEnd_txn_id_name) (1/2) nextDiskEnd_txn_id
  )%I as "HdiskEndMem_update".
  {
    iIntros; iNamed.
    iDestruct "Hinner" as "(%Hwf&Hmem&?&?&?&?)"; iNamed.
    iNamed "Hdisk".
    iNamed "Hdisk".
    iNamed "Hdurable".

    iDestruct (mono_nat_auth_own_agree with
      "HownDiskEndMem_logger HownDiskEndMem_walinv"
    ) as %[_ ->].
    iDestruct (mono_nat_auth_own_agree with
      "HownDiskEndMemTxn_logger HownDiskEndMemTxn_walinv"
    ) as %[_ ->].
    iDestruct (ghost_var_agree with
      "HownDiskEnd_logger HownDiskEnd_walinv"
    ) as %->.
    iDestruct (ghost_var_agree with
      "HownDiskEndTxn_logger HownDiskEndTxn_walinv"
    ) as %->.
    iCombine "HownDiskEndMem_linv HownDiskEndMem_walinv" as "HownDiskEndMem".
    iCombine "HownDiskEndMemTxn_linv HownDiskEndMemTxn_walinv" as "HownDiskEndMemTxn".
    iMod (mono_nat_own_update_halves (uint.nat (circΣ.diskEnd cs)) with
      "HownDiskEndMem_logger HownDiskEndMem"
    ) as "(HownDiskEndMem_logger&HownDiskEndMem&_)";
      first by lia.
    iMod (mono_nat_own_update_halves diskEnd_txn_id0 with
      "HownDiskEndMemTxn_logger HownDiskEndMemTxn"
    ) as "(HownDiskEndMemTxn_logger&HownDiskEndMemTxn&_)".
    {
      unshelve (epose proof (
        is_memLog_boundaries_region
        pmwrb_de pmwrb_pe _ _ _ _ _ _ Hcirc_matches _ _
      ) as Hreg).
      3: rewrite /pmwrb_de /pmwrb_pe; lia.
      3-4: reflexivity.
      simpl in Hreg.
      lia.
    }
    iDestruct "HownDiskEndMem" as
      "[HownDiskEndMem_linv HownDiskEndMem_walinv]"
    .
    iDestruct "HownDiskEndMemTxn" as
      "[HownDiskEndMemTxn_linv HownDiskEndMemTxn_walinv]"
    .

    iModIntro.
    iSplitR "
      HownDiskEndMem_linv HownDiskEndMemTxn_linv
      HownDiskEndMem_logger HownDiskEndMemTxn_logger
      HownDiskEnd_logger HownDiskEndTxn_logger
    "; last by iFrame.
    iFrame (Hwf) "∗#%".

    iPureIntro.
    simpl in Hcirc_matches.
    rewrite /circ_matches_txns /circΣ.diskEnd.
    replace (uint.nat _ - uint.nat _)%nat with (length (upds cs)) by word.
    eapply (is_memLog_boundaries_move _ _ _ pmwrb_de) in Hcirc_matches;
      last by reflexivity.
    assumption.
  }
  iMod ("HdiskEndMem_update" with "
    []
    Hinner
    HownDiskEndMem_linv HownDiskEndMemTxn_linv
    HownDiskEndMem_logger HownDiskEndMemTxn_logger
    HownDiskEnd_logger HownDiskEndTxn_logger
  ") as "Hupdate_post".
  {
    iPureIntro.
    word.
  }
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
  wp_apply (wp_Cond__Broadcast with "His_cond1").
  wp_loadField.
  wp_apply (wp_Cond__Broadcast with "His_cond2").
  wp_pures.
  iApply "HΦ".
  iFrame "His_locked".
  iSplitR "
    Hcirc_appender HnotLogging
    HownLoggerPos_logger HownLoggerTxn_logger
    HownDiskEndMem_logger HownDiskEndMemTxn_logger
    HownDiskEnd_logger HownDiskEndTxn_logger
  ".
  2: { by iFrame. }
  iExists (set diskEnd (λ _, uint.Z σ.(diskEnd) + uint.Z s.(Slice.sz))
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
    replace (uint.Z σ.(diskEnd) +
         (uint.nat σ.(memLog).(slidingM.mutable) - uint.nat σ.(diskEnd))%nat)
      with (uint.Z σ.(memLog).(slidingM.mutable)) by word.
    replace (W64 (uint.Z σ.(memLog).(slidingM.mutable))) with σ.(memLog).(slidingM.mutable) by word.
    by iFrame "∗ #".
  }

  iExists _, nextDiskEnd_txn_id0, _, _, _, _, _.
  iFrame. iModIntro.
  iClear "HinstalledTxn_lb".
  iNamed "Hlinv_pers".
  iFrame "HmemStart_txn HmemEnd_txn".
  iFrame "HnextDiskEnd_stable_old".
  iFrame "HinstalledTxn_lb".

  simpl.
  replace (uint.Z _ + uint.Z _) with (uint.Z σ.(memLog).(slidingM.mutable))
    by word.
  replace (uint.nat (uint.Z _)) with (uint.nat σ.(memLog).(slidingM.mutable))
    by word.
  replace (W64 _) with (σ.(memLog).(slidingM.mutable)) by word.
  iFrame.
  iSplit.
  { word. }
  iSplit.
  { iPureIntro. lia. }
  iSplit.
  {
    iPureIntro.
    assumption.
  }
  iSplit.
  2: done.
  iPureIntro.
  eapply (is_memLog_boundaries_move _ _ _ mwrb_de) in Htxns0;
    last by reflexivity.
  by assumption.
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
  wp_rec. wp_pures.
  iNamed "Hmem".
  iNamed "Hstfields".
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$]").
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
      { iFrame "∗#". }
      iIntros (progress) "(Hlkinv&Hlk_held&Hlogger)".
      wp_pures.
      wp_if_destruct.
      + wp_loadField.
        wp_apply (wp_Cond__Wait with "[$cond_logger $lk $Hlkinv $Hlk_held]").
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
  wp_apply (wp_Cond__Signal with "cond_shut").
  wp_loadField.
  wp_apply (wp_Mutex__Unlock with "[$lk $Hlk_held $Hlkinv]").
  wp_pures. by iApply ("HΦ" with "[//]").
Qed.

End goose_lang.
