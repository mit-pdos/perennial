From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgpreparer_repr bgpreparer_cquorum.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__quorumValidated (gpp : loc) ts gid γ :
    {{{ own_backup_gpreparer_vdm gpp ts gid γ ∗ own_backup_gpreparer_nrps gpp }}}
      BackupGroupPreparer__quorumValidated #gpp
    {{{ (vd : bool), RET #vd;
        own_backup_gpreparer_vdm gpp ts gid γ ∗
        own_backup_gpreparer_nrps gpp ∗
        if vd then quorum_validated γ gid ts else True
    }}}.
  Proof.
    iIntros (Φ) "[Hvdm Hnrps] HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) quorumValidated() bool {                @*)
    (*@     // Count the number of successful validation.                       @*)
    (*@     n := uint64(len(gpp.vdm))                                           @*)
    (*@     // Return if the transaction has been validated on a classic quorum. @*)
    (*@     return gpp.cquorum(n)                                               @*)
    (*@ }                                                                       @*)
    iNamed "Hvdm".
    wp_loadField.
    wp_apply (wp_MapLen with "Hvdm").
    iIntros "[%Hn Hvdm]".
    wp_apply (wp_BackupGroupPreparer__cquorum with "Hnrps").
    iIntros "Hnrps".
    iApply "HΦ".
    iFrame "∗ # %".
    case_bool_decide; last done.
    iExists (dom vdm).
    iFrame "Hvds".
    iPureIntro.
    split; first apply Hvincl.
    rewrite /cquorum_size size_dom. word.
  Qed.

End program.
