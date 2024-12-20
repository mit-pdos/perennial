From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import greader_repr.
  
Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupReader__reset (grd : loc) ts γ :
    {{{ own_greader_uninit grd }}}
      GroupReader__reset #grd
    {{{ RET #(); own_greader grd ts γ }}}.
  Proof.
    iIntros (Φ) "Hgrd HΦ".
    wp_rec.

    (*@ func (grd *GroupReader) reset() {                                       @*)
    (*@     grd.valuem = make(map[string]tulip.Value)                           @*)
    (*@     grd.qreadm = make(map[string]map[uint64]tulip.Version)              @*)
    (*@ }                                                                       @*)
    iNamed "Hgrd".
    wp_apply (wp_NewMap byte_string dbval).
    iIntros (valuemP') "Hvaluem".
    wp_storeField.
    wp_apply (wp_NewMap byte_string loc).
    iIntros (qreadmP') "Hqreadm".
    wp_storeField.
    iApply "HΦ".
    iFrame "∗ %".
    iModIntro.
    iExists ∅.
    by rewrite 2!big_sepM_empty big_sepM2_empty.
  Qed.

End program.
