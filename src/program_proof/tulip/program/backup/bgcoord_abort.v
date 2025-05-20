From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgcoord_repr bgcoord_finalized bgcoord_send bgcoord_get_leader bgcoord_change_leader.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupCoordinator__Abort (gcoord : loc) (tsW : u64) rk gid γ :
    let ts := uint.nat tsW in
    safe_abort γ ts -∗
    is_backup_gcoord gcoord rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__Abort #gcoord #tsW
    {{{ RET #(); True }}}.
  Proof.
    iIntros (ts) "#Habted #Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *BackupGroupCoordinator) Abort(ts uint64) {                @*)
    (*@     var leader = gcoord.GetLeader()                                     @*)
    (*@     gcoord.SendAbort(leader, ts)                                        @*)
    (*@     primitive.Sleep(params.NS_RESEND_ABORT)                             @*)
    (*@                                                                         @*)
    iNamed "Hgcoord".
    wp_apply (wp_BackupGroupCoordinator__GetLeader with "Hgcoord").
    iIntros (leader Hleader).
    wp_apply wp_ref_to; first by auto.
    iIntros (leaderP) "HleaderP".
    wp_load.
    wp_apply (wp_BackupGroupCoordinator__SendAbort with "Habted Hgcoord").
    { apply Hleader. }
    wp_apply wp_Sleep.

    (*@     for !gcoord.Finalized() {                                           @*)
    (*@         // Retry with different leaders until success.                  @*)
    (*@         leader = gcoord.ChangeLeader()                                  @*)
    (*@         gcoord.SendAbort(leader, ts)                                    @*)
    (*@         primitive.Sleep(params.NS_RESEND_ABORT)                         @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    set P := (λ _ : bool, ∃ leader' : u64, leaderP ↦[uint64T] #leader' ∗ ⌜leader' ∈ dom addrm⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [$HleaderP]"); last first; first 1 last.
    { done. }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      wp_apply (wp_BackupGroupCoordinator__Finalized with "[]").
      { iFrame "Hgcoord". }
      iIntros (finalized) "_".
      wp_pures.
      destruct finalized; wp_pures.
      { by iApply "HΦ". }
      iDestruct "HP" as (leader') "[HleaderP %Hin]".
      wp_apply (wp_BackupGroupCoordinator__ChangeLeader with "Hgcoord").
      iIntros (leadernew Hleadernew).
      wp_store.
      wp_load.
      wp_apply (wp_BackupGroupCoordinator__SendAbort with "Habted Hgcoord").
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
