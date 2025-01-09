From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr gcoord_register_finalization gcoord_finalized gcoord_send
  gcoord_get_leader gcoord_change_leader.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__Commit
    (gcoord : loc) (tsW : u64) (pwrsP : loc) q (pwrs : dbmap) gid γ :
    let ts := uint.nat tsW in
    safe_commit γ gid ts pwrs -∗
    is_gcoord gcoord gid γ -∗
    {{{ own_map pwrsP q pwrs }}}
      GroupCoordinator__Commit #gcoord #tsW #pwrsP
    {{{ RET #(); own_map pwrsP q pwrs }}}.
  Proof.
    iIntros (ts) "#Hcmted #Hgcoord".
    iIntros (Φ) "!> Hpwrs HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) Commit(ts uint64, pwrs tulip.KVMap) {   @*)
    (*@     gcoord.RegisterFinalization(ts)                                     @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupCoordinator__RegisterFinalization with "Hgcoord").

    (*@     var leader = gcoord.GetLeader()                                     @*)
    (*@     gcoord.SendCommit(leader, ts, pwrs)                                 @*)
    (*@     primitive.Sleep(params.NS_RESEND_COMMIT)                            @*)
    (*@                                                                         @*)
    iNamed "Hgcoord".
    wp_apply (wp_GroupCoordinator__GetLeader with "Hgcoord").
    iIntros (leader Hleader).
    wp_apply wp_ref_to; first by auto.
    iIntros (leaderP) "HleaderP".
    wp_load.
    wp_apply (wp_GroupCoordinator__SendCommit with "Hcmted Hgcoord Hpwrs").
    { apply Hleader. }
    iIntros "Hpwrs".
    wp_apply wp_Sleep.

    (*@     for !gcoord.Finalized(ts) {                                         @*)
    (*@         // Retry with different leaders until success.                  @*)
    (*@         leader = gcoord.ChangeLeader()                                  @*)
    (*@         gcoord.SendCommit(leader, ts, pwrs)                             @*)
    (*@         primitive.Sleep(params.NS_RESEND_COMMIT)                        @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    set P := (λ _ : bool, ∃ leader' : u64,
                 "HleaderP"  ∷ leaderP ↦[uint64T] #leader' ∗
                 "Hpwrs"     ∷ own_map pwrsP q pwrs ∗
                 "%Hinaddrm" ∷ ⌜leader' ∈ dom addrm⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [$Hpwrs $HleaderP]"); last first; first 1 last.
    { done. }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      wp_apply (wp_GroupCoordinator__Finalized with "[]").
      { iFrame "Hgcoord". }
      iIntros (finalized) "_".
      wp_pures.
      destruct finalized; wp_pures.
      { by iApply "HΦ". }
      iNamed "HP".
      wp_apply (wp_GroupCoordinator__ChangeLeader with "Hgcoord").
      iIntros (leadernew Hleadernew).
      wp_store.
      wp_load.
      wp_apply (wp_GroupCoordinator__SendCommit with "Hcmted Hgcoord Hpwrs").
      { apply Hleadernew. }
      iIntros "Hpwrs".
      wp_apply wp_Sleep.
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }
    iNamed 1.
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
