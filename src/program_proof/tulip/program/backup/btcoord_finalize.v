From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  btcoord_repr btcoord_stabilize btcoord_abort btcoord_resolve btcoord_commit.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupTxnCoordinator__Finalize tcoord ts γ :
    {{{ own_backup_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__Finalize #tcoord
    {{{ RET #(); own_backup_tcoord tcoord ts γ }}}.
  Proof.
    iIntros (Φ) "Htcoord HΦ".
    wp_rec.

    (*@ func (tcoord *BackupTxnCoordinator) Finalize() {                        @*)
    (*@     status, valid := tcoord.stabilize()                                 @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupTxnCoordinator__stabilize with "Htcoord").
    iIntros (status valid) "[Htcoord Hphase]".
    wp_pures.

    (*@     if !valid {                                                         @*)
    (*@         // Skip since a more recent backup txn coordinator is found.    @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct valid eqn:Hvalid; wp_pures; last first.
    { by iApply "HΦ". }

    (*@     if status == tulip.TXN_ABORTED {                                    @*)
    (*@         tcoord.abort()                                                  @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hcond; wp_pures.
    { destruct status eqn:Hstatus; [done | done | ].
      simpl.
      wp_apply (wp_BackupTxnCoordinator__abort with "Hphase Htcoord").
      iIntros "Htcoord".
      wp_pures.
      by iApply "HΦ".
    }

    (*@     // Possible @status: TXN_PREPARED and TXN_COMMITTED. Resolve the prophecy @*)
    (*@     // variable if @status == TXN_PREPARED.                             @*)
    (*@     tcoord.resolve(status)                                              @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupTxnCoordinator__resolve with "Hphase Htcoord").
    { by destruct status. }
    iIntros (ok) "[Htcoord #Hcmted]".
    wp_pures.
    destruct ok; wp_pures; last first.
    { by iApply "HΦ". }

    (*@     tcoord.commit()                                                     @*)
    (*@ }                                                                       @*)
    wp_apply (wp_BackupTxnCoordinator__commit with "Hcmted Htcoord").
    iIntros "Htcoord".
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
