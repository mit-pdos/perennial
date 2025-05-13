From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section leading.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__leading (px : loc) nidme nids γ :
    {{{ own_paxos px nidme nids γ }}}
      Paxos__leading #px
    {{{ (isleader : bool), RET #isleader;
        if isleader
        then own_paxos_leading px nidme nids γ
        else own_paxos px nidme nids γ
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) leading() bool {                                       @*)
    (*@     return px.isleader                                                  @*)
    (*@ }                                                                       @*)
    iNamed "Hpx". iNamed "Hleader".
    wp_loadField.
    iApply "HΦ".
    destruct isleader; iFrame "Hpx Hcand"; iFrame.
  Qed.

  Theorem wp_Paxos__leading__with_termc (px : loc) nidme termc nids γ :
    {{{ own_paxos_with_termc px nidme termc nids γ }}}
      Paxos__leading #px
    {{{ (isleader : bool), RET #isleader;
        if isleader
        then own_paxos_leading_with_termc px nidme termc nids γ
        else own_paxos px nidme nids γ
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) leading() bool {                                       @*)
    (*@     return px.isleader                                                  @*)
    (*@ }                                                                       @*)
    iNamed "Hpx". iNamed "Hleader".
    wp_loadField.
    iApply "HΦ".
    destruct isleader; iFrame "Hpx Hcand"; iFrame.
  Qed.

End leading.
