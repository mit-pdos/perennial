From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__HeartbeatSession (px : loc) nidme γ :
    is_paxos px nidme γ -∗
    {{{ True }}}
      Paxos__HeartbeatSession #px
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hpx" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) HeartbeatSession() {                                   @*)
    (*@     for {                                                               @*)
    (*@         primitive.Sleep(params.NS_HEARTBEAT_INTERVAL)                   @*)
    (*@         px.cv.Broadcast()                                               @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.
    iNamed "Hpx".
    wp_apply wp_Sleep.
    wp_loadField.
    wp_apply (wp_Cond__Broadcast with "Hcv").
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
