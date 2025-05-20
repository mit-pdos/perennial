From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__becomePreparing (gpp : loc) phase rk ts gid γ :
    {{{ own_backup_gpreparer_srespm gpp phase rk ts gid γ ∗
        own_backup_gpreparer_phase gpp phase
    }}}
      BackupGroupPreparer__becomePreparing #gpp
    {{{ RET #(); 
        own_backup_gpreparer_srespm gpp BGPPPreparing rk ts gid γ ∗
        own_backup_gpreparer_phase gpp BGPPPreparing
    }}}.
  Proof.
    iIntros (Φ) "[Hsrespm Hphase] HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) becomePreparing() {                     @*)
    (*@     gpp.srespm = make(map[uint64]bool)                                  @*)
    (*@     gpp.phase = BGPP_PREPARING                                          @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewMap.
    iIntros (srespmP) "Hsrespm'".
    iNamed "Hsrespm". iNamed "Hphase".
    do 2 wp_storeField.
    iModIntro.
    iApply "HΦ".
    iFrame.
    iSplit; last done.
    iSplit; last done.
    rewrite /prepare_responses dom_empty_L.
    by iApply big_sepS_empty.
  Qed.

End program.
