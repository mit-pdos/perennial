From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgpreparer_repr bgpreparer_try_resign.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__processQueryResult
    (gpp : loc) (rid : u64) (res : rpres) rk ts cid gid γ :
    query_outcome γ ts res -∗
    {{{ own_backup_gpreparer gpp rk ts cid gid γ }}}
      BackupGroupPreparer__processQueryResult #gpp #rid #(rpres_to_u64 res)
    {{{ RET #(); own_backup_gpreparer gpp rk ts cid gid γ }}}.
  Proof.
    iIntros "#Hquery" (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) processQueryResult(rid uint64, res uint64) { @*)
    (*@     gpp.tryResign(res)                                                  @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp".
    wp_apply (wp_BackupGroupPreparer__tryResign with "[] Hgpp").
    { by destruct res. }
    iIntros (resigned phase') "(Hgpp & %Hres & %Hresigned)".
    wp_pures.
    iApply "HΦ".
    by iFrame.
  Qed.

End program.
