From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupPreparer__getPhase (gpp : loc) phase ts gid γ :
    {{{ own_gpreparer_with_phase gpp phase ts gid γ }}}
      GroupPreparer__getPhase #gpp
    {{{ RET #(gppphase_to_u64 phase); 
        own_gpreparer_with_phase gpp phase ts gid γ ∗
        safe_gpreparer_phase γ ts gid phase
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) getPhase() uint64 {                           @*)
    (*@     return gpp.phase                                                    @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp". iNamed "Hphase".
    wp_loadField.
    rewrite Hphase.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

End program.
