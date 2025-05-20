From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgcoord_repr bgcoord_finalized bgcoord_get_pwrs
  bgcoord_send bgcoord_get_leader bgcoord_change_leader.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupCoordinator__Commit (gcoord : loc) (tsW : u64) rk gid γ :
    let ts := uint.nat tsW in
    is_txn_committed_ex γ ts -∗
    know_tulip_inv γ -∗
    is_backup_gcoord gcoord rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__Commit #gcoord #tsW
    {{{ RET #(); True }}}.
  Proof.
    iIntros (ts) "#Hcmted #Hinv #Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *BackupGroupCoordinator) Commit(ts uint64) {               @*)
    (*@     pwrs, ok := gcoord.GetPwrs()                                        @*)
    (*@     if !ok {                                                            @*)
    (*@         // If the partial writes are not available, then there is nothing @*)
    (*@         // left to do. The reason is that @tcoord.stabilize completes only @*)
    (*@         // after all groups have reported their status, which can only be @*)
    (*@         // TXN_COMMITTED or TXN_PREPARED at this point. For the former case, @*)
    (*@         // the commit will eventually be applied by each replica; for the @*)
    (*@         // latter case, the write set is guaranteed to exist.           @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupGroupCoordinator__GetPwrs with "Hgcoord").
    iIntros (pwrsP ok) "Hpwrs".
    wp_pures.
    destruct ok; wp_pures; last by iApply "HΦ".

    iDestruct "Hcmted" as (wrs) "Hcmted".
    iDestruct "Hpwrs" as (pwrs) "[#Hpwrs #Hsafepwrs]".
    iDestruct "Hsafepwrs" as (wrs') "[Hwrs' %Hsafe]".
    destruct Hsafe as (Hvts & Hvwrs & Hne & Hpwrs).
    (* Prove [wrs = wrs']. *)
    iDestruct "Hinv" as (proph) "Hinv".
    iAssert (|={⊤}=> (⌜wrs' = wrs⌝)%nat)%I as "Heqwrs".
    { iInv "Hinv" as "> HinvO" "HinvC".
      iNamed "HinvO". do 2 iNamed "Htxnsys".
      iDestruct (txn_res_lookup with "Hresm Hcmted") as %Hwrs.
      iDestruct (big_sepM_lookup with "Hvr") as "Hcmt".
      { apply Hwrs. }
      iDestruct "Hcmt" as "[Hwrs _]".
      iDestruct (txn_wrs_agree with "Hwrs Hwrs'") as %Heq.
      iMod ("HinvC" with "[-]").
      { by iFrame "Hkeys Hgroups Hrgs ∗ # %". }
      done.
    }
    iMod "Heqwrs" as %->.

    (*@     var leader = gcoord.GetLeader()                                     @*)
    (*@     gcoord.SendCommit(leader, ts, pwrs)                                 @*)
    (*@     primitive.Sleep(params.NS_RESEND_COMMIT)                            @*)
    (*@                                                                         @*)
    iNamed "Hgcoord".
    wp_apply (wp_BackupGroupCoordinator__GetLeader with "Hgcoord").
    iIntros (leader Hleader).
    wp_apply wp_ref_to; first by auto.
    iIntros (leaderP) "HleaderP".
    wp_load.
    
    wp_apply (wp_BackupGroupCoordinator__SendCommit with "[] Hgcoord Hpwrs").
    { apply Hleader. }
    { iFrame "# %".
      iPureIntro.
      by eapply wrs_group_elem_of_ptgroups.
    }
    iIntros "_".
    wp_apply wp_Sleep.

    (*@     for !gcoord.Finalized() {                                           @*)
    (*@         // Retry with different leaders until success.                  @*)
    (*@         leader = gcoord.ChangeLeader()                                  @*)
    (*@         gcoord.SendCommit(leader, ts, pwrs)                             @*)
    (*@         primitive.Sleep(params.NS_RESEND_COMMIT)                        @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    set P := (λ _ : bool, ∃ leader' : u64,
                 "HleaderP"  ∷ leaderP ↦[uint64T] #leader' ∗
                 "%Hinaddrm" ∷ ⌜leader' ∈ dom addrm⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [$HleaderP]"); last first; first 1 last.
    { done. }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      wp_apply (wp_BackupGroupCoordinator__Finalized with "[$Hgcoord]").
      iIntros (finalized) "_".
      wp_pures.
      destruct finalized; wp_pures.
      { by iApply "HΦ". }
      iNamed "HP".
      wp_apply (wp_BackupGroupCoordinator__ChangeLeader with "Hgcoord").
      iIntros (leadernew Hleadernew).
      wp_store.
      wp_load.
      wp_apply (wp_BackupGroupCoordinator__SendCommit with "[] Hgcoord Hpwrs").
      { apply Hleadernew. }
      { iFrame "# %".
        iPureIntro.
        by eapply wrs_group_elem_of_ptgroups.
      }
      iIntros "_".
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
