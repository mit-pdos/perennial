From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgcoord_repr bgpreparer_repr bgpreparer_action.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupCoordinator__NextPrepareAction gcoord (rid : u64) rk ts gid γ :
    is_backup_gcoord gcoord rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__NextPrepareAction #gcoord #rid
    {{{ (action : bgppaction), RET #(bgppaction_to_u64 action);
        safe_backup_gpreparer_action γ ts gid rk action
    }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *BackupGroupCoordinator) NextPrepareAction(rid uint64) uint64 { @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     a := gcoord.gpp.action(rid)                                         @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@     return a                                                            @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    iNamed "Hgcoord". iNamed "Hgpp".
    wp_loadField.
    wp_apply (wp_BackupGroupPreparer__action with "Hgpp").
    iIntros (action) "[Hgpp #Hsafea]".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked ∗". }
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
