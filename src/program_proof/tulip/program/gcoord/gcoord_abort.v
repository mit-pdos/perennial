From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr gcoord_register_finalization gcoord_finalized gcoord_send
  gcoord_get_leader gcoord_change_leader.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__Abort (gcoord : loc) (tsW : u64) gid γ :
    let ts := uint.nat tsW in
    safe_abort γ ts -∗
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__Abort #gcoord #tsW
    {{{ RET #(); True }}}.
  Proof.
    iIntros (ts) "#Habted #Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) Abort(ts uint64) {                      @*)
    (*@     gcoord.RegisterFinalization(ts)                                     @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupCoordinator__RegisterFinalization with "Hgcoord").
    iNamed "Hgcoord".

    (*@     var leader = gcoord.GetLeader()                                     @*)
    (*@     gcoord.SendAbort(leader, ts)                                        @*)
    (*@     primitive.Sleep(params.NS_RESEND_ABORT)                             @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupCoordinator__GetLeader with "Hgcoord").
    iIntros (leader Hleader).
    wp_apply wp_ref_to; first by auto.
    iIntros (leaderP) "HleaderP".
    wp_load.
    wp_apply (wp_GroupCoordinator__SendAbort with "Habted Hgcoord").
    { apply Hleader. }
    wp_apply wp_Sleep.

    (*@     for !gcoord.Finalized(ts) {                                         @*)
    (*@         // Retry with different leaders until success.                  @*)
    (*@         leader = gcoord.ChangeLeader()                                  @*)
    (*@         gcoord.SendAbort(leader, ts)                                    @*)
    (*@         primitive.Sleep(params.NS_RESEND_ABORT)                         @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)


    (*@     for !gcoord.Finalized(ts) {                                         @*)
    (*@         gcoord.SendAbort(leader, ts)                                    @*)
    (*@         primitive.Sleep(params.NS_RESEND_ABORT)                         @*)
    (*@         // Retry with different leaders until success.                  @*)
    (*@         leader = gcoord.ChangeLeader()                                  @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    set P := (λ _ : bool, ∃ leader' : u64, leaderP ↦[uint64T] #leader' ∗ ⌜leader' ∈ dom addrm⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [$HleaderP]"); last first; first 1 last.
    { done. }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      wp_apply (wp_GroupCoordinator__Finalized with "[]").
      { iFrame "Hgcoord". }
      iIntros (finalized) "_".
      wp_pures.
      destruct finalized; wp_pures.
      { by iApply "HΦ". }
      iDestruct "HP" as (leader') "[HleaderP %Hin]".
      wp_apply (wp_GroupCoordinator__ChangeLeader with "Hgcoord").
      iIntros (leadernew Hleadernew).
      wp_store.
      wp_load.
      wp_apply (wp_GroupCoordinator__SendAbort with "Habted Hgcoord").
      { apply Hleadernew. }
      wp_apply wp_Sleep.
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }
    iIntros "_".
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
