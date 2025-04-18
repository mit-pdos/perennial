From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__getPwrs (gpp : loc) ts gid γ :
    {{{ own_backup_gpreparer_pwrs gpp ts gid γ }}}
      BackupGroupPreparer__getPwrs #gpp
    {{{ (pwrsP : loc) (pwrsok : bool), RET (#pwrsP, #pwrsok);
        own_backup_gpreparer_pwrs gpp ts gid γ ∗
        if pwrsok
        then ∃ pwrs, own_map pwrsP DfracDiscarded pwrs ∗ safe_txn_pwrs γ gid ts pwrs
        else True
    }}}.
  Proof.
    iIntros (Φ) "Hpwrs HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) getPwrs() (tulip.KVMap, bool) {         @*)
    (*@     return gpp.pwrs, gpp.pwrsok                                         @*)
    (*@ }                                                                       @*)
    iNamed "Hpwrs".
    do 2 wp_loadField.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame "∗ # %".
    destruct pwrsok; last done.
    by eauto.
  Qed.

  Theorem wp_BackupGroupPreparer__getPwrs_external (gpp : loc) rk ts cid gid γ :
    {{{ own_backup_gpreparer gpp rk ts cid gid γ }}}
      BackupGroupPreparer__getPwrs #gpp
    {{{ (pwrsP : loc) (pwrsok : bool), RET (#pwrsP, #pwrsok);
        own_backup_gpreparer gpp rk ts cid gid γ ∗
        if pwrsok
        then ∃ pwrs, own_map pwrsP DfracDiscarded pwrs ∗ safe_txn_pwrs γ gid ts pwrs
        else True
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    do 2 iNamed "Hgpp".
    wp_apply (wp_BackupGroupPreparer__getPwrs with "Hpwrs").
    iIntros (pwrsP pwrsok) "[Hpwrs Hm]".
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

End program.
