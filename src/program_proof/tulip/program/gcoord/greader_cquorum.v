From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program Require Import quorum.
From Perennial.program_proof.tulip.program.gcoord Require Import greader_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupReader__cquorum (grd : loc) (n : u64) :
    {{{ own_greader_nrps grd }}}
      GroupReader__cquorum #grd #n
    {{{ RET #(bool_decide (size rids_all / 2 < uint.Z n)); own_greader_nrps grd }}}.
  Proof.
    iIntros (Φ) "Hgrd HΦ".
    wp_rec.

    (*@ func (grd *GroupReader) cquorum(n uint64) bool {                        @*)
    (*@     return quorum.ClassicQuorum(grd.nrps) <= n                          @*)
    (*@ }                                                                       @*)
    iNamed "Hgrd".
    wp_loadField.
    wp_apply wp_ClassicQuorum.
    iIntros (x Hx).
    wp_pures.
    case_bool_decide as Hc1.
    { case_bool_decide as Hc2; last word.
      iApply "HΦ". by iFrame "∗ %".
    }
    { case_bool_decide as Hc2; first word.
      iApply "HΦ". by iFrame "∗ %".
    }
  Qed.

End program.
