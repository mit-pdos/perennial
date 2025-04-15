From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__countProposals (gpp : loc) pps rk ts cid gid γ :
    {{{ own_backup_gpreparer_pps gpp pps rk ts cid gid γ }}}
      BackupGroupPreparer__countProposals #gpp
    {{{ (n : u64), RET #n; 
        own_backup_gpreparer_pps gpp pps rk ts cid gid γ ∗
        ⌜uint.nat n = size pps⌝
    }}}.
  Proof.
    iIntros (Φ) "Hpps HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) countProposals() uint64 {               @*)
    (*@     return uint64(len(gpp.pps))                                         @*)
    (*@ }                                                                       @*)
    iNamed "Hpps".
    wp_loadField.
    wp_apply (wp_MapLen with "Hpps").
    iIntros "[%Hsz Hpps]".
    iApply "HΦ".
    iFrame "∗ # %".
    word.
  Qed.

End program.
