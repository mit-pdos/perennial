From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr paxos_commit.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section learn.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__learn
    (px : loc) (lsn term : u64) (nidme : u64) (logc : list byte_string) nids γ :
    nidme ∈ nids ->
    length logc = uint.nat lsn ->
    safe_ledger_above γ nids (uint.nat term) logc -∗
    is_paxos_fname px nidme γ -∗
    know_paxos_file_inv γ nids -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos_following_with_termc px nidme term nids γ }}}
      Paxos__learn #px #lsn #term
    {{{ RET #(); own_paxos px nidme nids γ }}}.
  Proof.
    iIntros (Hnidme Hlenlogc) "#Hsafe #Hfname #Hinvfile #Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) learn(lsn uint64, term uint64) {                       @*)
    (*@     // Skip if the log term @px.terml does not match @lsn.              @*)
    (*@     if term != px.terml {                                               @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    wp_if_destruct.
    { iApply "HΦ".
      iFrame "Hcand Hleader".
      by iFrame "∗ # %".
    }

    (*@     px.commit(lsn)                                                      @*)
    (*@ }                                                                       @*)
    wp_apply (wp_Paxos__commit with "Hsafe Hfname Hinvfile Hinv [-HΦ]").
    { apply Hnidme. }
    { apply Hlenlogc. }
    { iFrame "Hcand Hleader".
      iFrame "∗ # %".
    }
    iIntros "Hpx".
    wp_pures.
    iApply "HΦ".
    iNamed "Hpx".
    by iFrame.
  Qed.

End learn.
