From Perennial.program_proof.rsm Require Import distx distx_replica.
From Goose.github_com.mit_pdos.rsm Require Import distx.

Section program.
  Context `{!heapGS Σ, !distx_ghostG Σ}.

  Definition is_rg (rg : loc) (gid : groupid) (γ : distx_names) : iProp Σ.
  Admitted.

  Theorem wp_ReplicaGroup__Abort (rg : loc) (ts : u64) (gid : groupid) γ :
    txnres_abt γ (uint.nat ts) -∗
    is_rg rg gid γ -∗
    {{{ True }}}
      ReplicaGroup__Abort #rg #ts
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (rg *ReplicaGroup) Abort(ts uint64) {                              @*)
    (*@     // Find the right replica to abort; retry until success.            @*)
    (*@     for {                                                               @*)
    (*@         rp := rg.rps[rg.leader]                                         @*)
    (*@         ok := rp.Abort(ts)                                              @*)
    (*@         if ok {                                                         @*)
    (*@             break                                                       @*)
    (*@         }                                                               @*)
    (*@         rg.changeLeader()                                               @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_ReplicaGroup__Commit (rg : loc) (ts : u64) (wrs : dbmap) (gid : groupid) γ :
    txnres_cmt γ (uint.nat ts) wrs -∗
    is_rg rg gid γ -∗
    {{{ True }}}
      ReplicaGroup__Commit #rg #ts
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (rg *ReplicaGroup) Commit(ts uint64) {                             @*)
    (*@     // Find the right replica to commit; retry until success.           @*)
    (*@     for {                                                               @*)
    (*@         rp := rg.rps[rg.leader]                                         @*)
    (*@         ok := rp.Commit(ts)                                             @*)
    (*@         if ok {                                                         @*)
    (*@             break                                                       @*)
    (*@         }                                                               @*)
    (*@         rg.changeLeader()                                               @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_ReplicaGroup__Prepare (rg : loc) (ts : u64) (gid : groupid) γ :
    is_rg rg gid γ -∗
    {{{ True }}}
      ReplicaGroup__Prepare #rg #ts
    {{{ (status : txnst), RET #(txnst_to_u64 status); group_txnst γ gid (uint.nat ts) status }}}.
  Proof.
    (*@ func (rg *ReplicaGroup) Prepare(ts uint64) uint64 {                     @*)
    (*@     var status uint64                                                   @*)
    (*@                                                                         @*)
    (*@     // Find the right replica to prepare; retry until success.          @*)
    (*@     for {                                                               @*)
    (*@         rp := rg.rps[rg.leader]                                         @*)
    (*@         s, ok := rp.Prepare(ts, slicem(rg.wrs))                         @*)
    (*@         if ok {                                                         @*)
    (*@             status = s                                                  @*)
    (*@             break                                                       @*)
    (*@         }                                                               @*)
    (*@         rg.changeLeader()                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     return status                                                       @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
