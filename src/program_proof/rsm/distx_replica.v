From Perennial.program_proof.rsm Require Import distx distx_txnlog.
From Goose.github_com.mit_pdos.rsm Require Import distx.

Section program.
  Context `{!heapGS Σ, !distx_ghostG Σ}.

  (*@ type Replica struct {                                                   @*)
  (*@     // Mutex                                                            @*)
  (*@     mu *sync.Mutex                                                      @*)
  (*@     // Replica ID.                                                      @*)
  (*@     rid uint64                                                          @*)
  (*@     // Replicated transaction log.                                      @*)
  (*@     log *TxnLog                                                         @*)
  (*@     //                                                                  @*)
  (*@     // Fields below are application states.                             @*)
  (*@     //                                                                  @*)
  (*@     // LSN up to which all commands have been applied.                  @*)
  (*@     lsna   uint64                                                       @*)
  (*@     // Preparation map.                                                 @*)
  (*@     prepm  map[uint64][]WriteEntry                                      @*)
  (*@     // Transaction status table; mapping from transaction timestamps to their @*)
  (*@     // commit/abort status.                                             @*)
  (*@     txntbl map[uint64]bool                                              @*)
  (*@     // Index.                                                           @*)
  (*@     idx    *Index                                                       @*)
  (*@     // Key-value map.                                                   @*)
  (*@     kvmap  map[string]*Tuple                                            @*)
  (*@ }                                                                       @*)
  Definition own_replica (rp : loc) (gid : groupid) (γ : distx_names) : iProp Σ :=
    ∃ (rid : u64) (log : loc) (lsna : u64) (prepm : loc) (txntbl : loc)
      (idx : loc) (kvmap : loc)
      (prepmM : gmap u64 Slice.t) (txntblM : gmap u64 bool)
      (kvmapM : gmap string loc),
      "Hrid"     ∷ rp ↦[Replica :: "rid"] #rid ∗
      "Hlog"     ∷ rp ↦[Replica :: "log"] #log ∗
      "Htxnlog"  ∷ own_txnlog log gid γ ∗
      "Hlsna"    ∷ rp ↦[Replica :: "lsna"] #lsna ∗
      "Hprepm"   ∷ rp ↦[Replica :: "prepm"] #prepm ∗
      "HprepmM"  ∷ own_map prepm (DfracOwn 1) prepmM ∗
      "Htxntbl"  ∷ rp ↦[Replica :: "txntbl"] #txntbl ∗
      "HtxntblM" ∷ own_map txntbl (DfracOwn 1) txntblM ∗
      "Hidx"     ∷ rp ↦[Replica :: "idx"] #idx ∗
      "Hkvmap"   ∷ rp ↦[Replica :: "kvmap"] #kvmap ∗
      "HkvmapM"  ∷ own_map kvmap (DfracOwn 1) kvmapM.

  Definition is_replica (rp : loc) (gid : groupid) (γ : distx_names) : iProp Σ :=
    ∃ (mu : loc),
      "#Hmu"   ∷ readonly (rp ↦[Replica :: "mu"] #mu) ∗
      "#Hlock" ∷ is_lock distxN #mu (own_replica rp gid γ) ∗
      "%Hgid"  ∷ ⌜gid ∈ gids_all⌝.

  Theorem wp_Replica__Abort (rp : loc) (ts : u64) (gid : groupid) γ :
    txnres_abt γ (uint.nat ts) -∗
    is_replica rp gid γ -∗
    {{{ True }}}
      Replica__Abort #rp #ts
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    (*@ func (rp *Replica) Abort(ts uint64) bool {                              @*)
    (*@     // Query the transaction table. Note that if there's an entry for @ts in @*)
    (*@     // @txntbl, then transaction @ts can only be aborted. That's why we're not @*)
    (*@     // even reading the value of entry.                                 @*)
    (*@     _, aborted := rp.txntbl[ts]                                         @*)
    (*@     if aborted {                                                        @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     lsn, term := rp.log.SubmitAbort(ts)                                 @*)
    (*@     if lsn == 0 {                                                       @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     safe := rp.log.WaitUntilSafe(lsn, term)                             @*)
    (*@     if !safe {                                                          @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     // We don't really care about the result, since at this point (i.e., after @*)
    (*@     // at least one failed prepares), abort should never fail.          @*)
    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Replica__Commit (rp : loc) (ts : u64) (wrs : dbmap) (gid : groupid) γ :
    txnres_cmt γ (uint.nat ts) wrs -∗
    is_replica rp gid γ -∗
    {{{ True }}}
      Replica__Commit #rp #ts
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    (*@ func (rp *Replica) Commit(ts uint64) bool {                             @*)
    (*@     // Query the transaction table. Note that if there's an entry for @ts in @*)
    (*@     // @txntbl, then transaction @ts can only be committed. That's why we're not @*)
    (*@     // even reading the value of entry.                                 @*)
    (*@     _, committed := rp.txntbl[ts]                                       @*)
    (*@     if committed {                                                      @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     lsn, term := rp.log.SubmitCommit(ts)                                @*)
    (*@     if lsn == 0 {                                                       @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     safe := rp.log.WaitUntilSafe(lsn, term)                             @*)
    (*@     if !safe {                                                          @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     // We don't really care about the result, since at this point (i.e., after @*)
    (*@     // all the successful prepares), commit should never fail.          @*)
    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Replica__Prepare (rp : loc) (ts : u64) (wrs : Slice.t) (gid : groupid) γ :
    is_replica rp gid γ -∗
    {{{ True }}}
      Replica__Prepare #rp #ts (to_val wrs)
    {{{ (status : txnst) (ok : bool), RET (#(txnst_to_u64 status), #ok);
        if ok then group_txnst γ gid (uint.nat ts) status else True
    }}}.
  Proof.
    (*@ func (rp *Replica) Prepare(ts uint64, wrs []WriteEntry) (uint64, bool) { @*)
    (*@     // Return immediately if the transaction has already prepared, aborted, or @*)
    (*@     // committed. Note that this is more of an optimization to eliminate @*)
    (*@     // submitting unnecessary log entries than a correctness requirement. We'll @*)
    (*@     // check this in @applyPrepare anyway.                              @*)
    (*@     status := rp.queryTxnStatus(ts)                                     @*)
    (*@     if status != TXN_RUNNING {                                          @*)
    (*@         return status, true                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     lsn, term := rp.log.SubmitPrepare(ts, wrs)                          @*)
    (*@     if lsn == 0 {                                                       @*)
    (*@         return 0, false                                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     safe := rp.log.WaitUntilSafe(lsn, term)                             @*)
    (*@     if !safe {                                                          @*)
    (*@         return 0, false                                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     rp.waitUntilExec(lsn)                                               @*)
    (*@                                                                         @*)
    (*@     // The command has been executed, get the prepared result. Note that here we @*)
    (*@     // can assume the transaction could not be running; we should indeed prove @*)
    (*@     // that to save some work from the users.                           @*)
    (*@     return rp.queryTxnStatus(ts), true                                  @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Replica__Read (rp : loc) (ts : u64) (key : string) (gid : groupid) γ :
    is_replica rp gid γ -∗
    {{{ True }}}
      Replica__Read #rp #ts #(LitString key)
    {{{ (v : dbval) (ok : bool), RET (dbval_to_val v, #ok);
        if ok then hist_repl_at γ key (uint.nat ts) v else True
    }}}.
  Proof.
    (*@ func (rp *Replica) Read(ts uint64, key string) (Value, bool) {          @*)
    (*@     // If the transaction has already terminated, this can only be an outdated @*)
    (*@     // read that no one actually cares.                                 @*)
    (*@     _, terminated := rp.txntbl[ts]                                      @*)
    (*@     if terminated {                                                     @*)
    (*@         return Value{}, false                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     lsn, term := rp.log.SubmitRead(ts, key)                             @*)
    (*@     if lsn == 0 {                                                       @*)
    (*@         return Value{}, false                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     safe := rp.log.WaitUntilSafe(lsn, term)                             @*)
    (*@     if !safe {                                                          @*)
    (*@         return Value{}, false                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     rp.waitUntilExec(lsn)                                               @*)
    (*@                                                                         @*)
    (*@     tpl := rp.idx.GetTuple(key)                                         @*)
    (*@                                                                         @*)
    (*@     // Note that @ReadVersion is read-only; in particular, it does not modify @*)
    (*@     // @tslast. This follows the key RSM principle that requires the application @*)
    (*@     // state to be exactly equal to applying some prefix of the replicated log. @*)
    (*@     v, ok := tpl.ReadVersion(ts)                                        @*)
    (*@                                                                         @*)
    (*@     return v, ok                                                        @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Replica__Start (rp : loc) (gid : groupid) γ :
    know_distx_inv γ -∗ 
    is_replica rp gid γ -∗
    {{{ True }}}
      Replica__Start #rp
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hinv #Hrp" (Φ) "!> _ HΦ".
    wp_call.

    wp_apply (wp_forBreak (λ _, True)%I); last first.
    { wp_pures. by iApply "HΦ". }
    (*@ func (rp *Replica) Start() {                                            @*)
    (*@     for {                                                               @*)
    (*@         rp.mu.Lock()                                                    @*)
    (*@                                                                         @*)
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_call.
    iNamed "Hrp".
    wp_loadField.
    wp_apply (acquire_spec with "Hlock").
    iIntros "[Hlocked Hrp]".
    wp_pures.
    iNamed "Hrp".

    (*@         lsn := rp.lsna + 1                                              @*)
    (*@         // TODO: a more efficient interface would return multiple safe commands @*)
    (*@         // at once (so as to reduce the frequency of acquiring Paxos mutex). @*)
    (*@                                                                         @*)
    wp_loadField. wp_pures.

    (*@         // Ghost action: Learn a list of new commands.                  @*)
    (*@         cmd, ok := rp.log.Lookup(lsn)                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_TxnLog__Lookup with "Htxnlog").
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    (* take the group invariant out *)
    assert (Hgids : gids_all !! gid = Some gid) by admit.
    iDestruct (big_sepL_lookup_acc with "Hgroups") as "[Hgroup Hgroups]"; first apply Hgids.
    iRename "Hlog" into "Hlog'".
    iNamed "Hgroup".

    (*@         if !ok {                                                        @*)
    (*@             // Sleep for 1 ms.                                          @*)
    (*@             rp.mu.Unlock()                                              @*)
    (*@             machine.Sleep(1 * 1000000)                                  @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    (*@         rp.apply(cmd)                                                   @*)
    (*@                                                                         @*)
    (*@         rp.lsna = lsn                                                   @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
