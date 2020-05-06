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

Theorem wp_Walog__logAppend l γ σₛ :
  {{{ readonly (l ↦[Walog.S :: "memLock"] #σₛ.(memLock)) ∗
      readonly (l ↦[Walog.S :: "condLogger"] #σₛ.(condLogger)) ∗
      readonly (l ↦[Walog.S :: "condInstall"] #σₛ.(condInstall)) ∗
      is_cond σₛ.(condLogger) #σₛ.(memLock) ∗
      is_cond σₛ.(condInstall) #σₛ.(memLock) ∗
      readonly (l ↦[Walog.S :: "st"] #σₛ.(wal_st)) ∗
      wal_linv σₛ.(wal_st) γ ∗
      locked γ.(lock_name) ∗
      is_lock N γ.(lock_name) #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ)
  }}}
    Walog__logAppend #l
  {{{ (progress:bool), RET #progress;
      wal_linv σₛ.(wal_st) γ ∗
      locked γ.(lock_name)
  }}}.
Proof.
  iIntros (Φ) "(#HmemLock& #HcondLogger& #HcondInstall &
              #His_cond1 & #His_cond2 & #Hf & Hlkinv& Hlocked& #His_lock) HΦ".
  wp_call.
  wp_bind (For _ _ _).
  (* TODO: need inner part of wal_linv with fixed memLog, so we can say after
  this wait loop [length memLog ≤ Z.of_nat LogSz] *)
  iNamed "Hlkinv".
  wp_apply (wp_forBreak_cond
              (λ b, "Hlocked" ∷ locked γ.(lock_name) ∗
                    "*" ∷ ∃ σ, "Hfields" ∷ wal_linv_fields σₛ.(wal_st) σ ∗
                               "HmemLog_linv" ∷ memLog_linv γ σ.(memLog) ∗
                               "#HdiskEnd_at_least'" ∷ diskEnd_at_least γ.(circ_name) (int.val σ.(diskEnd)) ∗
                               "#Hstart_at_least'" ∷ start_at_least γ.(circ_name) σ.(memLog).(slidingM.start) ∗
                               "%Hbreak" ∷ ⌜b = false → (length σ.(memLog).(slidingM.log) ≤ LogSz)⌝
              )%I
              with "[] [$Hlocked Hfields HmemLog_linv]").
  2: {
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
      iClear "HdiskEnd_at_least Hstart_at_least".
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
  (* TODO: move the rest of this function into a separate function, which gets
  to assume there is space in the log *)
  specialize (Hbreak eq_refl).
Admitted.

Theorem wp_Walog__logger l γ :
  {{{ is_wal P l γ }}}
    Walog__logger #l
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hwal HΦ".
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
  wp_apply (wp_forBreak_cond (fun b => wal_linv σₛ.(wal_st) γ ∗ locked γ.(lock_name))%I
              with "[] [$Hlkinv $Hlk_held]").
  { iIntros "!>" (Φ') "(Hlkinv&Hlk_held) HΦ".
    wp_apply (wp_load_shutdown with "[$st $Hlkinv]"); iIntros (shutdown) "Hlkinv".
    wp_pures.
    wp_if_destruct.
    - wp_pures.
      wp_apply (wp_Walog__logAppend with "[$Hlkinv $Hlk_held]").
      { iFrame "#". }
      iIntros (progress) "(Hlkinv&Hlk_held)".
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
  iIntros "(Hlkinv&Hlk_held)".
  wp_apply util_proof.wp_DPrintf.
  wp_apply (wp_dec_nthread with "[$st $Hlkinv]"); iIntros "Hlkinv".
  wp_loadField.
  wp_apply (wp_condSignal with "cond_shut").
  wp_loadField.
  wp_apply (release_spec with "[$lk $Hlk_held $Hlkinv]").
  iApply ("HΦ" with "[//]").
Qed.

End goose_lang.
