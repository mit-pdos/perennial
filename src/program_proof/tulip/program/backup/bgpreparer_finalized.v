From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (* A weak spec since its use is not related to safety *)
  Theorem wp_BackupGroupPreparer__finalized gpp rk ts cid gid γ :
    {{{ own_backup_gpreparer gpp rk ts cid gid γ }}}
      BackupGroupPreparer__finalized #gpp
    {{{ (finalized : bool), RET #finalized; own_backup_gpreparer gpp rk ts cid gid γ }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) finalized() bool {                      @*)
    (*@     return BGPP_COMMITTED <= gpp.phase                                  @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgpp". iNamed "Hphase".
    wp_loadField.
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.


End program.
