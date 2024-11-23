From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupPreparer__in (gpp : loc) (phase : gppphase) ts gid γ :
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__in #gpp #(gppphase_to_u64 phase)
    {{{ (ok : bool), RET #ok; 
        if ok
        then own_gpreparer_with_phase gpp phase ts gid γ
        else own_gpreparer gpp ts gid γ
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) in(phase uint64) bool {                       @*)
    (*@     return gpp.phase == phase                                           @*)
    (*@ }                                                                       @*)
    rename phase into phasearg.
    do 2 iNamed "Hgpp". iNamed "Hphase".
    wp_loadField.
    wp_pures.
    iApply "HΦ".
    case_bool_decide as Hok; last first.
    { by iFrame "∗ # %". }
    symmetry in Hok. inv Hok.
    by iFrame "∗ # %".
  Qed.

End program.
