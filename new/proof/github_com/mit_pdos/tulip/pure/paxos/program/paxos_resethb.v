From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section resethb.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__resethb (px : loc) nidme nids γ :
    {{{ own_paxos px nidme nids γ }}}
      Paxos__resethb #px
    {{{ RET #(); own_paxos px nidme nids γ }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) resethb() {                                            @*)
    (*@     px.hb = false                                                       @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_storeField.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    by iFrame "∗ # %".
  Qed.

End resethb.
