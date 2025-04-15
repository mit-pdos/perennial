From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgcoord_repr bgpreparer_get_pwrs.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupCoordinator__GetPwrs (gcoord : loc) rk ts gid γ :
    is_backup_gcoord gcoord rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__GetPwrs #gcoord
    {{{ (pwrsP : loc) (ok : bool), RET (#pwrsP, #ok); 
        if ok 
        then ∃ pwrs, own_map pwrsP DfracDiscarded pwrs ∗ safe_txn_pwrs γ gid ts pwrs
        else True
    }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *BackupGroupCoordinator) GetPwrs() (tulip.KVMap, bool) {   @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     pwrs, ok := gcoord.gpp.getPwrs()                                    @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@     return pwrs, ok                                                     @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    iNamed "Hgcoord". iNamed "Hgpp".
    wp_loadField.
    wp_apply (wp_BackupGroupPreparer__getPwrs_external with "Hgpp").
    iIntros (pwrsP pwrsok) "[Hgpp #Hpwrs]".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked ∗". }
    wp_pures.
    iModIntro.
    by iApply "HΦ".
  Qed.

End program.
