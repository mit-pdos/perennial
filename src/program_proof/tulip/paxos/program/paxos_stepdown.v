From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Perennial.program_proof.tulip.paxos.invariance Require Import prepare.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section stepdown.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__stepdown px (nidme term : u64) termc nids γ :
    nidme ∈ nids ->
    uint.Z termc ≤ uint.Z term < 2 ^ 64 ->
    know_paxos_inv γ nids -∗
    {{{ own_paxos_with_termc px nidme termc nids γ }}}
      Paxos__stepdown #px #term
    {{{ RET #(); own_paxos_following_with_termc px nidme term nids γ }}}.
  Proof.
    iIntros (Hnidme Hlt) "#Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec. wp_pures.

    (*@ func (px *Paxos) stepdown(term uint64) {                                @*)
    (*@     px.termc = term                                                     @*)
    (*@     px.iscand = false                                                   @*)
    (*@     px.isleader = false                                                 @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx". iNamed "Hcand". iNamed "Hleader".
    do 3 wp_storeField.

    (*@     // TODO: Write @px.termc to disk.                                   @*)
    (*@                                                                         @*)
    (*@     // Logical action: Prepare(@term).                                  @*)
    (*@ }                                                                       @*)
    destruct (decide (termc = term)) as [-> | Hne].
    { (* Case: [termc = term]. No logical updates required. *)
      iApply "HΦ".
      iFrame "HiscandP HisleaderP".
      by iFrame "∗ # %".
    }
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (paxos_inv_prepare (uint.nat term) with "Htermc Hterml Hlogn HinvO")
      as "(Htermc & Hterml & Hlogn & HinvO & Hlsnp & #Hpromise)".
    { apply Hnidme. }
    { word. }
    iMod ("HinvC" with "HinvO") as "_".
    iApply "HΦ".
    iFrame "HisleaderP HiscandP".
    assert (Htermlc' : uint.Z terml ≤ uint.Z term) by word.
    iFrame "∗ # %".
    iClear "Hpreped Hlsnp".
    by case_decide.
  Qed.

End stepdown.
