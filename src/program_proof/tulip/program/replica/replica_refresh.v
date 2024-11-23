From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_finalized replica_last_proposal replica_acquire
  replica_accept replica_log.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__refresh (rp : loc) (ts : u64) (rank : u64) gid rid γ α :
    {{{ own_replica rp gid rid γ α }}}
      Replica__refresh #rp #ts #rank
    {{{ RET #(); own_replica rp gid rid γ α }}}.
  Proof.
    iIntros (Φ) "Hrp HΦ".
    wp_rec. wp_pures. by iApply "HΦ".
    (*@ func (rp *Replica) refresh(ts uint64, rank uint64) {                    @*)
    (*@     // TODO                                                             @*)
    (*@ }                                                                       @*)
  Qed.

End program.
