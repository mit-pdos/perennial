From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__collectProposal
    (gpp : loc) (rid : u64) (pp : ppsl) pps rk ts cid gid γ :
    rid ∈ rids_all ->
    is_replica_backup_vote γ gid rid ts rk cid -∗
    latest_proposal_replica γ gid rid ts rk (uint.nat pp.1) pp.2 -∗
    {{{ own_backup_gpreparer_pps gpp pps rk ts cid gid γ }}}
      BackupGroupPreparer__collectProposal #gpp #rid (ppsl_to_val pp)
    {{{ RET #(); own_backup_gpreparer_pps gpp (<[rid := pp]> pps) rk ts cid gid γ }}}.
  Proof.
    iIntros (Hrid) "#Hvote #Hlatest".
    iIntros (Φ) "!> Hpps HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) collectProposal(rid uint64, pp tulip.PrepareProposal) { @*)
    (*@     gpp.pps[rid] = pp                                                   @*)
    (*@ }                                                                       @*)
    iNamed "Hpps".
    wp_loadField.
    wp_apply (wp_MapInsert with "Hpps"); first done.
    iIntros "Hpps".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iNamed "Hlatest".
    iDestruct (big_sepM_insert_2 with "[] Hblts") as "Hblts'".
    { by iFrame "Hlb". }
    iClear "Hblts".
    iFrame "∗ # %".
    iSplit.
    { by iApply big_sepM_insert_2. }
    iSplit.
    { rewrite dom_insert_L.
      by iApply big_sepS_insert_2.
    }
    iPureIntro.
    split.
    { rewrite dom_insert_L. clear -Hrid Hdompps. set_solver. }
    split.
    { by apply map_Forall_insert_2. }
    { by apply map_Forall2_insert_2. }
  Qed.

  Theorem wp_BackupGroupPreparer__collectProposal_weak
    (gpp : loc) (rid : u64) (pp : ppsl) pps rk ts cid gid γ :
    rid ∈ rids_all ->
    is_replica_backup_vote γ gid rid ts rk cid -∗
    latest_proposal_replica γ gid rid ts rk (uint.nat pp.1) pp.2 -∗
    {{{ own_backup_gpreparer_pps gpp pps rk ts cid gid γ }}}
      BackupGroupPreparer__collectProposal #gpp #rid (ppsl_to_val pp)
    {{{ (pps' : gmap u64 ppsl), RET #(); 
        own_backup_gpreparer_pps gpp pps' rk ts cid gid γ
    }}}.
  Proof.
    iIntros (Hrid) "#Hvote #Hlatest".
    iIntros (Φ) "!> Hpps HΦ".
    by wp_apply (wp_BackupGroupPreparer__collectProposal with "Hvote Hlatest Hpps").
  Qed.

End program.
