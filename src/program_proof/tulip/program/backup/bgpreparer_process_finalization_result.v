From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgpreparer_repr bgpreparer_stop.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__processFinalizationResult
    (gpp : loc) (res : rpres) rk ts cid gid γ :
    {{{ own_backup_gpreparer gpp rk ts cid gid γ }}}
      BackupGroupPreparer__processFinalizationResult #gpp #(rpres_to_u64 res)
    {{{ RET #(); own_backup_gpreparer gpp rk ts cid gid γ }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) processFinalizationResult(res uint64) { @*)
    (*@     if res == tulip.REPLICA_WRONG_LEADER {                              @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@     gpp.stop()                                                          @*)
    (*@ }                                                                       @*)
    wp_pures.
    case_bool_decide; wp_pures.
    { by iApply "HΦ". }
    do 2 iNamed "Hgpp".
    wp_apply (wp_BackupGroupPreparer__stop with "Hphase").
    iIntros "Hphase".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame "∗ #". simpl.
    iSplit.
    { iApply (own_backup_gpreparer_srespm_non_accepting_phase with "Hsrespm").
      intros [].
    }
    done.
  Qed.

End program.
