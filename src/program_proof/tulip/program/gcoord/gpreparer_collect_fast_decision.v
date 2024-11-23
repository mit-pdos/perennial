From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupPreparer__collectFastDecision
    (gpp : loc) (rid : u64) (b : bool) ts gid γ :
    rid ∈ rids_all ->
    is_replica_pdec_at_rank γ gid rid ts O b -∗
    (if b then is_replica_validated_ts γ gid rid ts else True) -∗
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__collectFastDecision #gpp #rid #b
    {{{ RET #(); own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros (Hrid) "#Hpdec #Hvd".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) collectFastDecision(rid uint64, b bool) {     @*)
    (*@     gpp.frespm[rid] = b                                                 @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgpp". iNamed "Hfrespm".
    wp_loadField.
    wp_apply (wp_MapInsert with "Hfrespm"); first done.
    iIntros "Hfrespm".
    wp_pures.
    iApply "HΦ".
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { iApply (big_sepM_insert_2 with "[] Hfast"). iFrame "#". }
    iPureIntro.
    rewrite dom_insert_L.
    set_solver.
  Qed.

End program.
