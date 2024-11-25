From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program Require Import quorum.
From Perennial.program_proof.tulip.program.gcoord Require Import gpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupPreparer__fquorum (gpp : loc) (n : u64) :
    {{{ own_gpreparer_nrps gpp }}}
      GroupPreparer__fquorum #gpp #n
    {{{ RET #(bool_decide (((3 * size rids_all + 3) / 4 ≤ uint.Z n) ∧ size rids_all ≠ O));
        own_gpreparer_nrps gpp
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) fquorum(n uint64) bool {                      @*)
    (*@     return quorum.FastQuorum(gpp.nrps) <= n                             @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp".
    wp_loadField.
    wp_apply wp_FastQuorum.
    { rewrite size_rids_all in Hnrps. word. }
    iIntros (x Hx).
    wp_pures.
    case_bool_decide as Hc1.
    { case_bool_decide as Hc2; last word.
      iApply "HΦ". by iFrame "∗ %".
    }
    { case_bool_decide as Hc2.
      { exfalso.
        apply Classical_Prop.not_and_or in Hc1.
        destruct Hc1 as [Hc1 | Hz]; last first.
        { rewrite size_rids_all in Hz. lia. }
        word.
      }
      iApply "HΦ". by iFrame "∗ %".
    }
  Qed.

End program.
