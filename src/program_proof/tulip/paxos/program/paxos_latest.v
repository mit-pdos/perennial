From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section latest.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__latest (px : loc) nidme termc nids γ :
    {{{ own_paxos_following_with_termc px nidme termc nids γ }}}
      Paxos__latest #px
    {{{ (latest : bool), RET #latest;
        if latest
        then own_paxos_following_with_termc px nidme termc nids γ
        else ∃ terml, own_paxos_with_termc_terml px nidme termc terml nids γ ∧
                      ⌜termc ≠ terml⌝
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) latest() bool {                                        @*)
    (*@     return px.termc == px.terml                                         @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    do 2 wp_loadField.
    wp_pures.
    iApply "HΦ".
    case_bool_decide.
    - iFrame "Hcand Hleader".
      by iFrame "∗ # %".
    - iFrame "Hcand Hleader".
      iFrame "∗ # %".
      iPureIntro.
      by intros ->.
  Qed.

End latest.
