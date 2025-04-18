From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgcoord_repr bgpreparer_finalized.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupCoordinator__Finalized gcoord rk ts gid γ :
    is_backup_gcoord gcoord rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__Finalized #gcoord
    {{{ (finalized : bool), RET #finalized; True }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *BackupGroupCoordinator) Finalized() bool {                @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     done := gcoord.gpp.finalized()                                      @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@     return done                                                         @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    iNamed "Hgcoord". iNamed "Hgpp".
    wp_loadField.
    wp_apply (wp_BackupGroupPreparer__finalized with "Hgpp").
    iIntros (finalized) "Hgpp".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked ∗". }
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
