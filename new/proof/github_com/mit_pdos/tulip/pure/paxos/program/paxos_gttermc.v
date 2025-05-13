From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section gttermc.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__gttermc (px : loc) (term : u64) nidme termc nids γ :
    {{{ own_paxos_with_termc px nidme termc nids γ }}}
      Paxos__gttermc #px #term
    {{{ (invalid : bool), RET #invalid;
        own_paxos_with_termc px nidme termc nids γ ∗
        ⌜if invalid then True else uint.Z term ≤ uint.Z termc⌝
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) gttermc(term uint64) bool {                            @*)
    (*@     return px.termc < term                                              @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    wp_pures.
    iApply "HΦ".
    case_bool_decide as Horder.
    - iFrame "Hcand Hleader".
      by iFrame "∗ # %".
    - iFrame "Hcand Hleader".
      iFrame "∗ # %".
      iPureIntro.
      clear -Horder. word.
  Qed.

End gttermc.
