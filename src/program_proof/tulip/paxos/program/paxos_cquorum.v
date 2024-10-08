From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos quorum.

Section cquorum.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__cquorum (px : loc) (n : u64) nids :
    {{{ own_paxos_sc px nids }}}
      Paxos__cquorum #px #n
    {{{ (ok : bool), RET #ok; own_paxos_sc px nids ∗ ⌜size nids / 2 < uint.Z n⌝ }}}.
  Proof.
    (*@ func (px *Paxos) cquorum(n uint64) bool {                               @*)
    (*@     return quorum.ClassicQuorum(px.sc) <= n                             @*)
    (*@ }                                                                       @*)
  Admitted.

End cquorum.
