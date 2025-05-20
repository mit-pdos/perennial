From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gpreparer_repr.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__validate (gpp : loc) (rid : u64) ts gid γ :
    rid ∈ rids_all ->
    is_replica_validated_ts γ gid rid ts -∗
    {{{ own_backup_gpreparer_vdm gpp ts gid γ }}}
      BackupGroupPreparer__validate #gpp #rid
    {{{ RET #(); own_backup_gpreparer_vdm gpp ts gid γ }}}.
  Proof.
    iIntros (Hrid) "#Hvd".
    iIntros (Φ) "!> Hvdm HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) validate(rid uint64) {                  @*)
    (*@     gpp.vdm[rid] = true                                                 @*)
    (*@ }                                                                       @*)
    iNamed "Hvdm".
    wp_loadField.
    wp_apply (wp_MapInsert with "Hvdm"); first done.
    iIntros "Hvdm".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame "∗ # %".
    iSplit.
    { rewrite /validation_responses dom_insert_L.
      by iApply big_sepS_insert_2.
    }
    iPureIntro.
    rewrite dom_insert_L. set_solver.
  Qed.

End program.
