From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section gettermc.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__gettermc__following (px : loc) nidme termc nids γ :
    {{{ own_paxos_following_with_termc px nidme termc nids γ }}}
      Paxos__gettermc #px
    {{{ RET #termc; own_paxos_following_with_termc px nidme termc nids γ }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) gettermc() uint64 {                                    @*)
    (*@     return px.termc                                                     @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    iFrame "∗ # %".
  Qed.

  Theorem wp_Paxos__gettermc__nominated (px : loc) nidme termc nids γ :
    {{{ own_paxos_nominated_with_termc px nidme termc nids γ }}}
      Paxos__gettermc #px
    {{{ RET #termc; own_paxos_nominated_with_termc px nidme termc nids γ }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) gettermc() uint64 {                                    @*)
    (*@     return px.termc                                                     @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    iFrame "∗ # %".
  Qed.

  Theorem wp_Paxos__gettermc__leading (px : loc) nidme termc nids γ :
    {{{ own_paxos_leading_with_termc px nidme termc nids γ }}}
      Paxos__gettermc #px
    {{{ RET #termc; own_paxos_leading_with_termc px nidme termc nids γ }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) gettermc() uint64 {                                    @*)
    (*@     return px.termc                                                     @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    iFrame "∗ # %".
  Qed.

  Theorem wp_Paxos__gettermc__weak (px : loc) nidme nids γ :
    {{{ own_paxos px nidme nids γ }}}
      Paxos__gettermc #px
    {{{ (termc : u64), RET #termc; own_paxos px nidme nids γ }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) gettermc() uint64 {                                    @*)
    (*@     return px.termc                                                     @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    iFrame "∗ # %".
  Qed.

End gettermc.
