From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section heartbeat.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__heartbeat__following_with_termc (px : loc) nidme termc nids γ :
    {{{ own_paxos_following_with_termc px nidme termc nids γ }}}
      Paxos__heartbeat #px
    {{{ RET #(); own_paxos_following_with_termc px nidme termc nids γ }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) heartbeat() {                                          @*)
    (*@     px.hb = true                                                        @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_storeField.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    by iFrame "∗ # %".
  Qed.

  Theorem wp_Paxos__heartbeat (px : loc) nidme nids γ :
    {{{ own_paxos px nidme nids γ }}}
      Paxos__heartbeat #px
    {{{ RET #(); own_paxos px nidme nids γ }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) heartbeat() {                                          @*)
    (*@     px.hb = true                                                        @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_storeField.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    by iFrame "∗ # %".
  Qed.

End heartbeat.
