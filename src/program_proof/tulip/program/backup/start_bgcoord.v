From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgcoord_repr mk_bgcoord bgcoord_response_session.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_startBackupGroupCoordinator
    (addrmP : loc) (cid : coordid) (tsW rkW : u64) (addrm : gmap u64 chan) gid γ :
    let ts := uint.nat tsW in
    let rk := uint.nat rkW in
    (1 < rk)%nat ->
    gid ∈ gids_all ->
    dom addrm = rids_all ->
    own_map addrmP DfracDiscarded addrm -∗
    know_tulip_inv γ -∗
    know_tulip_network_inv γ gid addrm -∗
    {{{ own_replica_backup_token γ cid.1 cid.2 ts rk gid }}}
      startBackupGroupCoordinator #addrmP (coordid_to_val cid) #tsW #rkW
    {{{ (gcoord : loc), RET #gcoord;
        is_backup_gcoord_with_addrm gcoord addrm rk ts gid γ
    }}}.
  Proof.
    iIntros (ts rk Hrk Hgid Hdomaddrm) "#Haddrm #Hinv #Hinvnet".
    iIntros (Φ) "!> Htoken HΦ".
    wp_rec.

    (*@ func startBackupGroupCoorinator(addrm map[uint64]grove_ffi.Address, cid tulip.CoordID, ts, rank uint64) *BackupGroupCoordinator { @*)
    (*@     gcoord := mkBackupGroupCoordinator(addrm, cid, ts, rank)            @*)
    (*@                                                                         @*)
    wp_apply (wp_mkBackupGroupCoordinator with "Haddrm Hinv Hinvnet Htoken").
    { apply Hrk. }
    { apply Hgid. }
    { apply Hdomaddrm. }
    iIntros (gcoord) "#Hgcoord".

    (*@     for ridloop := range(addrm) {                                       @*)
    (*@         rid := ridloop                                                  @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.ResponseSession(rid)                                 @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_MapIter_fold _ _ _ (λ _ : gmap u64 chan, True)%I with "Haddrm []"); first done.
    { clear Φ.
      iIntros (m rid addr Φ) "!> [_ [_ %Haddr]] HΦ".
      wp_apply wp_fork; last by iApply "HΦ".
      wp_apply (wp_BackupGroupCoordinator__ResponseSession with "Hgcoord").
      { apply Haddr. }
      done.
    }

    (*@     return gcoord                                                       @*)
    (*@ }                                                                       @*)
    iIntros "_".
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
