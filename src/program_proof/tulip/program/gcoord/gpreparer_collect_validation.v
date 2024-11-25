From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupPreparer__collectValidation (gpp : loc) (rid : u64) phase ts gid γ :
    rid ∈ rids_all ->
    is_replica_validated_ts γ gid rid ts -∗
    {{{ own_gpreparer_with_phase gpp phase ts gid γ }}}
      GroupPreparer__collectValidation #gpp #rid
    {{{ RET #(); own_gpreparer_with_phase gpp phase ts gid γ }}}.
  Proof.
    iIntros (Hrid) "#Hvd".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) collectValidation(rid uint64) {               @*)
    (*@     gpp.vdm[rid] = true                                                 @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp". iNamed "Hvdm".
    wp_loadField.
    wp_apply (wp_MapInsert with "Hvdm"); first done.
    iIntros "Hvdm".
    wp_pures.
    iApply "HΦ".
    iFrame "Hfrespm ∗ # %".
    iModIntro.
    iSplit.
    { rewrite /validation_responses dom_insert_L.
      by iApply (big_sepS_insert_2 with "[] Hvalidation").
    }
    iPureIntro.
    rewrite dom_insert_L.
    set_solver.
  Qed.

End program.
