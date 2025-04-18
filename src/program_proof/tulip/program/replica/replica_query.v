From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_finalized replica_lowest_rank replica_refresh.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__query (rp : loc) (tsW : u64) (rankW : u64) gid rid γ α :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    gid ∈ gids_all ->
    know_tulip_inv γ -∗
    {{{ own_replica rp gid rid γ α }}}
      Replica__query #rp #tsW #rankW
    {{{ (res : rpres), RET #(rpres_to_u64 res);
        own_replica rp gid rid γ α ∗ query_outcome γ ts res
    }}}.
  Proof.
    iIntros (ts rank Hgid) "#Hinv".
    iIntros (Φ) "!> Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) query(ts uint64, rank uint64) uint64 {               @*)
    (*@     res, final := rp.finalized(ts)                                      @*)
    (*@     if final {                                                          @*)
    (*@         return res                                                      @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__finalized with "Hinv Hrp").
    { apply Hgid. }
    iIntros (res final) "[Hrp Hfinal]".
    wp_pures.
    destruct final; wp_pures.
    { iApply "HΦ". iFrame. by destruct res. }

    (*@     // Check if the coordinator is the most recent one. If not, report the @*)
    (*@     // existence of a more recent coordinator.                          @*)
    (*@     rankl, ok := rp.lowestRank(ts)                                      @*)
    (*@     if ok && rank < rankl {                                             @*)
    (*@         return tulip.REPLICA_STALE_COORDINATOR                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hrp".
    wp_apply (wp_Replica__lowestRank with "Hpsmrkm").
    iIntros (rankl ok) "[Hpsmrkm _]".
    wp_pures.
    destruct ok; wp_pures.
    { case_bool_decide as Hrank; wp_pures.
      { iApply ("HΦ" $! ReplicaStaleCoordinator).
        by iFrame "Hcm Hhistm Hcpm Hptsmsptsm ∗ # %".
      }
      iApply ("HΦ" $! ReplicaOK).
      by iFrame "Hcm Hhistm Hcpm Hptsmsptsm ∗ # %".
    }

    (*@     return tulip.REPLICA_OK                                             @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! ReplicaOK).
    by iFrame "Hcm Hhistm Hcpm Hptsmsptsm ∗ # %".
  Qed.

  Theorem wp_Replica__Query (rp : loc) (tsW : u64) (rankW : u64) gid rid γ :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    is_replica rp gid rid γ -∗
    {{{ True }}}
      Replica__Query #rp #tsW #rankW
    {{{ (res : rpres), RET #(rpres_to_u64 res); query_outcome γ ts res }}}.
  Proof.
    iIntros (ts rank) "#Hrp".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) Query(ts uint64, rank uint64) uint64 {               @*)
    (*@     rp.mu.Lock()                                                        @*)
    (*@     res := rp.query(ts, rank)                                           @*)
    (*@     rp.refresh(ts, rank)                                                @*)
    (*@     rp.mu.Unlock()                                                      @*)
    (*@     return res                                                          @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hrp]".
    iNamed "Hgidrid".
    wp_apply (wp_Replica__query with "[$Hinv] Hrp").
    { apply Hgid. }
    iIntros (res) "[Hrp #Hp]".
    wp_apply (wp_Replica__refresh with "Hrp").
    iIntros "Hrp".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hrp]").
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
