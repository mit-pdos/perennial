From Perennial.program_proof.rsm.distx Require Import prelude.
From Perennial.program_proof.rsm.distx.program Require Import replica txnlog.
From Goose.github_com.mit_pdos.rsm Require Import distx.

Section program.
  Context `{!heapGS Σ, !distx_ghostG Σ}.

  Definition is_rg (rg : loc) (gid : groupid) (γ : distx_names) : iProp Σ.
  Admitted.

  #[global]
  Instance is_rg_persistent rg gid γ :
    Persistent (is_rg rg gid γ).
  Admitted.

  Theorem wp_ReplicaGroup__changeLeader (rg : loc) :
    {{{ True }}}
      ReplicaGroup__changeLeader #rg
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (rg *ReplicaGroup) changeLeader() {                                @*)
    (*@     // TODO                                                             @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_ReplicaGroup__Abort (rg : loc) (ts : u64) (gid : groupid) γ :
    safe_abort γ (uint.nat ts) -∗
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

  Theorem wp_ReplicaGroup__Commit (rg : loc) (ts : u64) (gid : groupid) γ :
    safe_commit γ gid (uint.nat ts) -∗
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

  Theorem wp_ReplicaGroup__Read (rg : loc) (ts : u64) (key : byte_string) gid γ :
    safe_read gid (uint.nat ts) key ->
    is_rg rg gid γ -∗
    {{{ True }}}
      ReplicaGroup__Read #rg #ts #(LitString key)
    {{{ (value : dbval), RET (dbval_to_val value); hist_repl_at γ key (pred (uint.nat ts)) value }}}.
  Proof.
    (*@ func (rg *ReplicaGroup) Read(ts uint64, key string) Value {             @*)
    (*@     var value Value                                                     @*)
    (*@                                                                         @*)
    (*@     // Find the right replica to prepare; retry until success.          @*)
    (*@     for {                                                               @*)
    (*@         rp := rg.rps[rg.leader]                                         @*)
    (*@         v, ok := rp.Read(ts, key)                                       @*)
    (*@         if ok {                                                         @*)
    (*@             value = v                                                   @*)
    (*@             break                                                       @*)
    (*@         }                                                               @*)
    (*@         rg.changeLeader()                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     return value                                                        @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_ReplicaGroup__Prepare
    (rg : loc) (ts : u64) (pwrsS : Slice.t) (pwrsL : list dbmod) (pwrs : dbmap) gid γ :
    safe_prepare γ gid (uint.nat ts) pwrs -∗
    is_rg rg gid γ -∗
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs }}}
      ReplicaGroup__Prepare #rg #ts (to_val pwrsS)
    {{{ (st : txnst), RET #(txnst_to_u64 st); txn_token γ gid (uint.nat ts) st }}}.
  Proof.
    (*@ func (rg *ReplicaGroup) Prepare(ts uint64, pwrs []WriteEntry) uint64 {  @*)
    (*@     var status uint64                                                   @*)
    (*@                                                                         @*)
    (*@     // Find the right replica to prepare; retry until success.          @*)
    (*@     for {                                                               @*)
    (*@         rp := rg.rps[rg.leader]                                         @*)
    (*@         s, ok := rp.Prepare(ts, pwrs)                                   @*)
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
