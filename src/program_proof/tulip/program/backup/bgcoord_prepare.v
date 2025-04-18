From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgcoord_repr bgcoord_prepare_session bgcoord_wait_until_prepare_done.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupCoordinator__Prepare
    (gcoord : loc) (tsW : u64) (rkW : u64) (ptgsP : Slice.t)
    (ptgs : txnptgs) gid γ :
    let ts := uint.nat tsW in
    let rk := uint.nat rkW in
    valid_ts ts ->
    is_lnrz_tid γ ts -∗
    safe_txn_ptgs γ ts ptgs -∗
    is_txnptgs_in_slice ptgsP ptgs -∗
    is_backup_gcoord gcoord rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__Prepare #gcoord #tsW #rkW (to_val ptgsP)
    {{{ (phase : txnphase) (valid : bool), RET (#(txnphase_to_u64 phase), #valid); 
        if valid then safe_group_txnphase γ ts gid phase else True
    }}}.
  Proof.
    iIntros (ts rk Hvts) "#Hlnrz #Hsafeptgs #Hptgs #Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *BackupGroupCoordinator) Prepare(ts, rank uint64, ptgs []uint64) (uint64, bool) { @*)
    (*@     // Spawn a session with each replica.                               @*)
    (*@     for ridloop := range(gcoord.addrm) {                                @*)
    (*@         rid := ridloop                                                  @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.PrepareSession(rid, ts, rank, ptgs)                  @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hgcoord". iNamed "Haddrm".
    wp_loadField.
    wp_apply (wp_MapIter_fold _ _ _ (λ _, True)%I with "Haddrm []").
    { done. }
    { clear Φ.
      iIntros (mx rid c Φ) "!> [_ %Hrid] HΦ".
      destruct Hrid as [_ Hrid].
      wp_pures.
      iAssert (is_backup_gcoord_with_addrm gcoord addrm rk ts gid γ)%I as "#Hgcoord".
      { by iFrame "# %". }
      wp_apply wp_fork.
      { wp_apply (wp_BackupGroupCoordinator__PrepareSession with "Hlnrz Hsafeptgs Hptgs Hgcoord").
        { apply Hvts. }
        { by apply elem_of_dom_2 in Hrid. }
        done.
      }
      by iApply "HΦ".
    }
    iIntros "_".

    (*@     status, valid := gcoord.WaitUntilPrepareDone()                      @*)
    (*@     return status, valid                                                @*)
    (*@ }                                                                       @*)
    wp_apply wp_BackupGroupCoordinator__WaitUntilPrepareDone.
    { by iFrame "# %". }
    iIntros (status valid) "#Hsafep".
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
