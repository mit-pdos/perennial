From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section lttermc.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__lttermc (px : loc) (term : u64) nidme nids γ :
    {{{ own_paxos px nidme nids γ }}}
      Paxos__lttermc #px #term
    {{{ (outdated : bool), RET #outdated;
        if outdated
        then own_paxos px nidme nids γ
        else (∃ termc, own_paxos_with_termc px nidme termc nids γ ∧
                       ⌜uint.Z termc ≤ uint.Z term⌝)
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) lttermc(term uint64) bool {                            @*)
    (*@     return term < px.termc                                              @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    wp_pures.
    iApply "HΦ".
    case_bool_decide.
    - iFrame "Hcand Hleader".
      by iFrame "∗ # %".
    - iFrame "Hcand Hleader".
      iFrame "∗ # %".
      word.
  Qed.

End lttermc.
