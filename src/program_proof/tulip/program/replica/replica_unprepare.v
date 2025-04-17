From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_try_accept replica_refresh.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__Unprepare rp (tsW rankW : u64) gid rid γ :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    rank ≠ O ->
    is_group_prepare_proposal γ gid ts rank false -∗
    is_replica rp gid rid γ -∗
    {{{ True }}}
      Replica__Unprepare #rp #tsW #rankW
    {{{ (res : rpres), RET #(rpres_to_u64 res);
        accept_outcome γ gid rid ts rank false res
    }}}.
  Proof.
    iIntros (ts rank Hranknz) "#Hppsl #Hrp".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) Unprepare(ts uint64, rank uint64) uint64 {           @*)
    (*@     rp.mu.Lock()                                                        @*)
    (*@     res := rp.tryAccept(ts, rank, false)                                @*)
    (*@     rp.refresh(ts, rank)                                                @*)
    (*@     rp.mu.Unlock()                                                      @*)
    (*@     return res                                                          @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hrp]".
    iNamed "Hgidrid".
    wp_apply (wp_Replica__tryAccept with "Hppsl [$Hinv] Hinvfile Hrp").
    { apply Hgid. }
    { apply Hrid. }
    { apply Hranknz. }
    iIntros (res) "[Hrp #Hup]".
    wp_apply (wp_Replica__refresh with "Hrp").
    iIntros "Hrp".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hrp]").
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
