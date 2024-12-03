From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gcoord_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__ResendSession (gcoord : loc) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__ResendSession #gcoord
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) ResendSession() {                       @*)
    (*@     for {                                                               @*)
    (*@         primitive.Sleep(params.NS_RESEND_PREPARE)                       @*)
    (*@         gcoord.cvrs.Broadcast()                                         @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_apply wp_Sleep.
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Cond__Broadcast with "Hcvrs").
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
