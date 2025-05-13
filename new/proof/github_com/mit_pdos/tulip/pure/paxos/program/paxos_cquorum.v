From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Perennial.program_proof.tulip.program Require Import quorum.
From Goose.github_com.mit_pdos.tulip Require Import paxos quorum.

Section cquorum.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__cquorum (px : loc) (n : u64) nids :
    {{{ own_paxos_sc px nids }}}
      Paxos__cquorum #px #n
    {{{ RET #(bool_decide (size nids / 2 < uint.Z n)); own_paxos_sc px nids }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) cquorum(n uint64) bool {                               @*)
    (*@     return quorum.ClassicQuorum(px.sc) <= n                             @*)
    (*@ }                                                                       @*)
    iNamed "Hpx".
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

End cquorum.
