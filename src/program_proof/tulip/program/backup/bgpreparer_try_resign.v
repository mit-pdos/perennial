From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gpreparer_try_resign.
From Perennial.program_proof.tulip.program.backup Require Import
  bgpreparer_repr bgpreparer_ready.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.


  Theorem wp_BackupGroupPreparer__tryResign (gpp : loc) (res : rpres) phase rk ts cid gid γ :
    try_resign_requirement γ ts res -∗
    {{{ own_backup_gpreparer_with_phase gpp phase rk ts cid gid γ }}}
      BackupGroupPreparer__tryResign #gpp #(rpres_to_u64 res)
    {{{ (resigned : bool) (phase' : bgppphase), RET #resigned;
        own_backup_gpreparer_with_phase gpp phase' rk ts cid gid γ ∗
        ⌜(if resigned then True else not_finalizing_rpres res)⌝ ∗
        ⌜resigned = bool_decide (bgpp_ready phase')⌝
    }}}.
  Proof.
    iIntros "#Hreq" (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) tryResign(res uint64) bool {            @*)
    (*@     if gpp.ready() {                                                    @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupGroupPreparer__ready_external with "Hgpp").
    iIntros "Hgpp".
    case_bool_decide as Hready; wp_pures.
    { iApply "HΦ".
      case_bool_decide; last done.
      by iFrame.
    }
    iNamed "Hgpp". iNamed "Hphase".
                
    (*@     if res == tulip.REPLICA_COMMITTED_TXN {                             @*)
    (*@         gpp.phase = BGPP_COMMITTED                                      @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hcommitted; wp_pures.
    { wp_storeField.
      iModIntro.
      iApply "HΦ".
      destruct res; try done. simpl.
      iDestruct (own_backup_gpreparer_srespm_non_accepting_phase _ _ BGPPCommitted with "Hsrespm")
        as "Hsrespm".
      { intros []. }
      by iFrame "∗ #".
    }

    (*@     if res == tulip.REPLICA_ABORTED_TXN {                               @*)
    (*@         gpp.phase = BGPP_ABORTED                                        @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Haborted; wp_pures.
    { wp_storeField.
      iModIntro.
      iApply "HΦ".
      destruct res; try done. simpl.
      iDestruct (own_backup_gpreparer_srespm_non_accepting_phase _ _ BGPPAborted with "Hsrespm")
        as "Hsrespm".
      { intros []. }
      by iFrame "∗ #".
    }

    (*@     if res == tulip.REPLICA_STALE_COORDINATOR {                         @*)
    (*@         gpp.phase = BGPP_STOPPED                                        @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hstopped; wp_pures.
    { wp_storeField.
      iModIntro.
      iApply "HΦ".
      destruct res; try done. simpl.
      iDestruct (own_backup_gpreparer_srespm_non_accepting_phase _ _ BGPPStopped with "Hsrespm")
        as "Hsrespm".
      { intros []. }
      by iFrame.
    }

    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! false phase).
    case_bool_decide; first done.
    iFrame "∗ # %".
    iPureIntro.
    by destruct res.
  Qed.

End program.
