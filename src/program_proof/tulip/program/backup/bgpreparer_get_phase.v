From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__getPhase (gpp : loc) phase rk ts cid gid γ :
    {{{ own_backup_gpreparer_with_phase gpp phase rk ts cid gid γ }}}
      BackupGroupPreparer__getPhase #gpp
    {{{ RET #(bgppphase_to_u64 phase); 
        own_backup_gpreparer_with_phase gpp phase rk ts cid gid γ ∗
        safe_backup_gpreparer_phase γ ts cid gid rk phase
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) getPhase() uint64 {                     @*)
    (*@     return gpp.phase                                                    @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp". iNamed "Hphase".
    wp_loadField.
    rewrite Hphase.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

End program.
