From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__stop (gpp : loc) phase :
    {{{ own_backup_gpreparer_phase gpp phase }}}
      BackupGroupPreparer__stop #gpp
    {{{ RET #(); own_backup_gpreparer_phase gpp BGPPStopped }}}.
  Proof.
    iIntros (Φ) "Hphase HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) stop()  {                               @*)
    (*@     gpp.phase = BGPP_STOPPED                                            @*)
    (*@ }                                                                       @*)
    iNamed "Hphase".
    wp_storeField.
    iApply "HΦ".
    by iFrame.
  Qed.

End program.
