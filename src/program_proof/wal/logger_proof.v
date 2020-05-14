From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names (Σ:=Σ)).
Implicit Types (s: log_state.t) (memLog: slidingM.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let circN := walN .@ "circ".

Theorem wp_Walog__waitForSpace l γ σₛ :
  {{{ "#HmemLock" ∷ readonly (l ↦[Walog.S :: "memLock"] #σₛ.(memLock)) ∗
      "#HcondLogger" ∷ readonly (l ↦[Walog.S :: "condLogger"] #σₛ.(condLogger)) ∗
      "#HcondInstall" ∷ readonly (l ↦[Walog.S :: "condInstall"] #σₛ.(condInstall)) ∗
      "#His_cond1" ∷ is_cond σₛ.(condLogger) #σₛ.(memLock) ∗
      "#His_cond2" ∷ is_cond σₛ.(condInstall) #σₛ.(memLock) ∗
      "#?" ∷ readonly (l ↦[Walog.S :: "st"] #σₛ.(wal_st)) ∗
      "Hlkinv" ∷ wal_linv σₛ.(wal_st) γ ∗
      "Hlocked" ∷ locked γ.(lock_name) ∗
      "#His_lock" ∷ is_lock N γ.(lock_name) #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ)
  }}}
    Walog__waitForSpace #l
  {{{ σ, RET #();
      "Hlocked" ∷ locked γ.(lock_name)  ∗
      "Hfields" ∷ wal_linv_fields σₛ.(wal_st) σ ∗
      "HmemLog_linv" ∷ memLog_linv γ σ.(memLog) ∗
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
              (λ b, "Hlocked" ∷ locked γ.(lock_name) ∗
                    "*" ∷ ∃ σ, "Hfields" ∷ wal_linv_fields σₛ.(wal_st) σ ∗
                               "HmemLog_linv" ∷ memLog_linv γ σ.(memLog) ∗
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
    change (int.val (word.divu (word.sub 4096 8) 8)) with LogSz.
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

Theorem wp_Walog__logAppend l circ_l γ σₛ :
  {{{ "#HmemLock" ∷ readonly (l ↦[Walog.S :: "memLock"] #σₛ.(memLock)) ∗
      "#HcondLogger" ∷ readonly (l ↦[Walog.S :: "condLogger"] #σₛ.(condLogger)) ∗
      "#HcondInstall" ∷ readonly (l ↦[Walog.S :: "condInstall"] #σₛ.(condInstall)) ∗
      "#d" ∷ readonly (l ↦[Walog.S :: "d"] σₛ.(wal_d)) ∗
      "#circ" ∷ readonly (l ↦[Walog.S :: "circ"] #σₛ.(circ)) ∗
      "#His_cond1" ∷ is_cond σₛ.(condLogger) #σₛ.(memLock) ∗
      "#His_cond2" ∷ is_cond σₛ.(condInstall) #σₛ.(memLock) ∗
      "#?" ∷ readonly (l ↦[Walog.S :: "st"] #σₛ.(wal_st)) ∗
      "#His_lock" ∷ is_lock N γ.(lock_name) #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ) ∗
      "#Hwal" ∷ is_wal P l γ ∗
      "Hlkinv" ∷ wal_linv σₛ.(wal_st) γ ∗
      "Hlocked" ∷ locked γ.(lock_name) ∗
      "Hlogger" ∷ logger_inv γ circ_l
  }}}
    Walog__logAppend #l #circ_l
  {{{ (progress:bool), RET #progress;
      wal_linv σₛ.(wal_st) γ ∗
      locked γ.(lock_name) ∗
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
    iFrame "Hlocked HnotLogging Happender".
    iExists _; iFrame.
    iExists _; iFrame "% ∗".
  }
  iNamed "HdiskEnd_circ".
  iMod (thread_own_get with "HdiskEnd_exactly HnotLogging") as "(HdiskEnd_exactly&HdiskEnd_is&HareLogging)".
  iNamed "HmemLog_linv".
  iNamed "Hstart_circ".
  iDestruct "HmemStart_txn" as "#HmemStart_txn".
  iDestruct "HnextDiskEnd_txn" as "#HnextDiskEnd_txn".
  iMod (txn_pos_valid_locked with "Hwal HmemStart_txn Howntxns") as "(%HmemStart_txn&Howntxns)".
  iMod (txn_pos_valid_locked with "Hwal HnextDiskEnd_txn Howntxns") as "(%HnextDiskEnd_txn&Howntxns)".
  (* XXX: should duplicate monotonicity of txns to lock invariant *)
  iMod (get_txns_are _ _ _ _ memStart_txn_id (S nextDiskEnd_txn_id) with "Howntxns Hwal") as "[Htxns_are Howntxns]"; eauto.
  { admit. }
  (* use this to also strip a later *)
  wp_apply (wp_loadField_ro with "HmemLock").
  iDestruct "Htxns_are" as "#Htxns_are".
  wp_apply (release_spec with "[-HΦ HareLogging HdiskEnd_is Happender Hbufs $His_lock $Hlocked]").
  { iExists _; iFrame "# ∗".
    iSplitR "Howntxns HmemEnd_txn".
    - iExists _; iFrame "% ∗".
    - iExists _, _, _; iFrame "# % ∗". }
  wp_loadField.
  iDestruct "Hwal" as "[Hwal Hcirc]".
  wp_apply (wp_circular__Append _ _ (emp) with "[$Hbufs $HdiskEnd_is $Happender $Hcirc $Hstart_at_least]").
  { rewrite subslice_length; word. }
  { rewrite subslice_length; word. }

  { (* Append fupd *)
    rewrite /circular_pred.
    iIntros (cs) "(%Hcirc_wf&Hcirc_ctx)".
    iIntros (cs' [] [Htrans Hcirc_wf']).
    simpl in Htrans; monad_inv.
    iInv "Hwal" as (σs) "[Hinner HP]".
    { admit. (* TODO: adjust namespaces *) }

    iDestruct "Hinner" as "(>%Hwf&Hmem&Htxns_ctx&>?&>?)".
    iNamed.
    iNamed "Hdisk".
    iDestruct (ghost_var_agree with "Hcirc_ctx Howncs") as %Heq; subst cs0.
    iMod (txns_are_sound with "Htxns_ctx Htxns_are") as "(%Htxns_are & Htxns_ctx)"; first by solve_ndisj.
    iMod (ghost_var_update _ with "Hcirc_ctx Howncs") as "[$ Howncs]".
    iModIntro.
    iSplitL; [ | done ].
    iNext.
    iExists _; iFrame.
    iSplitR; auto.
    iExists _; iFrame.
    iNamed "Hdisk".
    iExists installed_txn_id, nextDiskEnd_txn_id.
    iFrame "# ∗".
    (* TODO: extend is_durable and is_durable_txn *)
Admitted.

Theorem wp_Walog__logger l circ_l γ :
  {{{ "#Hwal" ∷ is_wal P l γ ∗
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
  wp_apply (wp_forBreak_cond (fun b => wal_linv σₛ.(wal_st) γ ∗ locked γ.(lock_name) ∗ logger_inv γ circ_l)%I
              with "[] [$]").
  { iIntros "!>" (Φ') "(Hlkinv&Hlk_held&Hlogger) HΦ"; iNamed "Hlogger".
    wp_apply (wp_load_shutdown with "[$st $Hlkinv]"); iIntros (shutdown) "Hlkinv".
    wp_pures.
    wp_if_destruct.
    - wp_pures.
      wp_apply (wp_Walog__logAppend with "[$Hlkinv $Hlk_held $HnotLogging $Happender]").
      { iFrame "# ∗". }
      iIntros (progress) "(Hlkinv&Hlk_held&HnotLogging)".
      wp_pures.
      destruct (negb progress); [ wp_if_true | wp_if_false ]; wp_pures.
      + wp_loadField.
        wp_apply (wp_condWait with "[$cond_logger $lk $Hlkinv $Hlk_held]").
        iIntros "(Hlk_held&Hlkinv)".
        wp_pures.
        iApply ("HΦ" with "[$]").
      + iApply ("HΦ" with "[$]").
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
