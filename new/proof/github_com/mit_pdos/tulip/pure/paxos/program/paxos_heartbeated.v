From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section heartbeated.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__heartbeated (px : loc) nidme nids γ :
    {{{ own_paxos px nidme nids γ }}}
      Paxos__heartbeated #px
    {{{ (hb : bool), RET #hb; own_paxos px nidme nids γ }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) heartbeated() bool {                                   @*)
    (*@     return px.hb                                                        @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    by iFrame "∗ # %".
  Qed.

End heartbeated.
