From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__setPwrs (gpp : loc) (pwrsP : loc) (pwrs : dbmap) ts gid γ :
    own_map pwrsP DfracDiscarded pwrs -∗
    safe_txn_pwrs γ gid ts pwrs -∗
    {{{ own_backup_gpreparer_pwrs gpp ts gid γ }}}
      BackupGroupPreparer__setPwrs #gpp #pwrsP
    {{{ RET #(); own_backup_gpreparer_pwrs gpp ts gid γ }}}.
  Proof.
    iIntros "#Hm #Hsafe" (Φ) "!> Hpwrs HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) setPwrs(pwrs tulip.KVMap) {             @*)
    (*@     gpp.pwrsok = true                                                   @*)
    (*@     gpp.pwrs = pwrs                                                     @*)
    (*@ }                                                                       @*)
    iNamed "Hpwrs".
    do 2 wp_storeField.
    iApply "HΦ".
    by iFrame "∗ #".
  Qed.

End program.
