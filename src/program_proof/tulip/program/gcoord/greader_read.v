From Perennial.program_proof.tulip.invariance Require Import read.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import greader_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupReader__read (grd : loc) (key : byte_string) ts γ :
    {{{ own_greader grd ts γ }}}
      GroupReader__read #grd #(LitString key)
    {{{ (v : dbval) (ok : bool), RET (dbval_to_val v, #ok); 
        own_greader grd ts γ ∗
        if ok then fast_or_quorum_read γ key ts v else True
    }}}.
  Proof.
    iIntros (Φ) "Hgrd HΦ".
    wp_rec.

    (*@ func (grd *GroupReader) read(key string) (tulip.Value, bool) {          @*)
    (*@     v, ok := grd.valuem[key]                                            @*)
    (*@     return v, ok                                                        @*)
    (*@ }                                                                       @*)
    iNamed "Hgrd". iNamed "Hvaluem".
    wp_loadField.
    wp_apply (wp_MapGet with "Hvaluem").
    iIntros (v ok) "[%Hok Hvaluem]".
    wp_pures.
    iApply "HΦ".
    iFrame "∗ #".
    destruct ok; last done.
    apply map_get_true in Hok.
    by iApply (big_sepM_lookup with "Hfinal").
  Qed.

End program.
