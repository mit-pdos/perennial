From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__ready (gpp : loc) phase :
    {{{ own_backup_gpreparer_phase gpp phase }}}
      BackupGroupPreparer__ready #gpp
    {{{ RET #(bool_decide (bgpp_ready phase)); own_backup_gpreparer_phase gpp phase }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) ready() bool {                          @*)
    (*@     return BGPP_PREPARED <= gpp.phase                                   @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp".
    wp_loadField.
    wp_pures.
    rewrite /bgppphase_to_u64 in Hphase.
    rewrite /bgpp_ready.
    case_bool_decide as Hcond.
    { case_bool_decide as Hret.
      { iApply "HΦ". by iFrame. }
      destruct phase; word.
    }
    { case_bool_decide as Hret; last first.
      { iApply "HΦ". by iFrame. }
      destruct phase; word.
    }
  Qed.

  Theorem wp_BackupGroupPreparer__ready_external (gpp : loc) phase rk ts cid gid γ :
    {{{ own_backup_gpreparer_with_phase gpp phase rk ts cid gid γ }}}
      BackupGroupPreparer__ready #gpp
    {{{ RET #(bool_decide (bgpp_ready phase)); 
        own_backup_gpreparer_with_phase gpp phase rk ts cid gid γ
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    iNamed "Hgpp".
    wp_apply (wp_BackupGroupPreparer__ready with "Hphase").
    iIntros "Hphase".
    iApply "HΦ".
    by iFrame "∗ #".
  Qed.

End program.
