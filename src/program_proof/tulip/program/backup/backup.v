From Perennial.program_proof.tulip.program Require Import prelude.

Section repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition own_tcoord (tcoord : loc) (ts : nat) (γ : tulip_names) : iProp Σ.
  Admitted.

End repr.

Section repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupTxnCoordinator__stabilize tcoord ts γ :
    {{{ own_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__stabilize #tcoord
    {{{ (status : txnphase) (valid : bool), RET (#(txnphase_to_u64 status), #valid); 
        own_tcoord tcoord ts γ ∗
        if valid then safe_txnphase γ ts status else True
    }}}.
  Proof.
    (*@ func (tcoord *BackupTxnCoordinator) stabilize() (uint64, bool) {        @*)
    (*@     ts := tcoord.ts                                                     @*)
    (*@     rank := tcoord.rank                                                 @*)
    (*@     ptgs := tcoord.ptgs                                                 @*)
    (*@                                                                         @*)
    (*@     mu := new(sync.Mutex)                                               @*)
    (*@     cv := sync.NewCond(mu)                                              @*)
    (*@     // Number of groups that have responded (i.e., groups whose prepare status @*)
    (*@     // is determined).                                                  @*)
    (*@     var nr uint64 = 0                                                   @*)
    (*@     // Number of groups that have prepared.                             @*)
    (*@     var np uint64 = 0                                                   @*)
    (*@     var st uint64 = tulip.TXN_PREPARED                                  @*)
    (*@     var vd bool = true                                                  @*)
    (*@                                                                         @*)
    (*@     for _, gcoordloop := range(tcoord.gcoords) {                        @*)
    (*@         gcoord := gcoordloop                                            @*)
    (*@                                                                         @*)
    (*@         go func() {                                                     @*)
    (*@             stg, vdg := gcoord.Prepare(ts, rank, ptgs)                  @*)
    (*@                                                                         @*)
    (*@             mu.Lock()                                                   @*)
    (*@             nr += 1                                                     @*)
    (*@             if !vdg {                                                   @*)
    (*@                 vd = false                                              @*)
    (*@             } else if stg == tulip.TXN_PREPARED {                       @*)
    (*@                 np += 1                                                 @*)
    (*@             } else {                                                    @*)
    (*@                 st = stg                                                @*)
    (*@             }                                                           @*)
    (*@             mu.Unlock()                                                 @*)
    (*@             cv.Signal()                                                 @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     // Wait until either a higher-ranked coordinator is found (i.e., as @*)
    (*@     // indicated by @valid = false), or all participant groups have responded. @*)
    (*@     //                                                                  @*)
    (*@     // A note on the difference between this method and @txn.preapre. Unlike @*)
    (*@     // @txn.prepare() where it's OK (and good for performance) to terminate this @*)
    (*@     // phase once the transaction status is determined, the backup txn  @*)
    (*@     // coordinator should wait until it finds out the status of all participant @*)
    (*@     // groups to finalize the transaction outcome for every group.      @*)
    (*@     mu.Lock()                                                           @*)
    (*@     for vd && nr != uint64(len(tcoord.gcoords)) {                       @*)
    (*@         cv.Wait()                                                       @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     // Use the invariant saying that "if @st = TXN_PREPARED, then @np = @nr" to @*)
    (*@     // establish the postcondition.                                     @*)
    (*@                                                                         @*)
    (*@     status := st                                                        @*)
    (*@     valid := vd                                                         @*)
    (*@     mu.Unlock()                                                         @*)
    (*@                                                                         @*)
    (*@     return status, valid                                                @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupTxnCoordinator__abort tcoord ts γ :
    is_txn_aborted γ ts -∗
    {{{ own_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__abort #tcoord
    {{{ RET #(); own_tcoord tcoord ts γ }}}.
  Proof.
    (*@ func (tcoord *BackupTxnCoordinator) abort() {                           @*)
    (*@     for _, gcoordloop := range(tcoord.gcoords) {                        @*)
    (*@         gcoord := gcoordloop                                            @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.Abort(tcoord.ts)                                     @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupTxnCoordinator__resolve tcoord status ts γ :
    status ≠ TxnAborted ->
    {{{ own_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__resolve #tcoord #(txnphase_to_u64 status)
    {{{ RET #(); own_tcoord tcoord ts γ ∗ is_txn_committed_ex γ ts }}}.
  Proof.
    (*@ func (tcoord *BackupTxnCoordinator) resolve(status uint64) {            @*)
    (*@     if status == tulip.TXN_PREPARED {                                   @*)
    (*@         // Logical action: Commit.                                      @*)
    (*@         trusted_proph.ResolveCommit(tcoord.proph, tcoord.ts, tcoord.mergeWrites()) @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupTxnCoordinator__commit tcoord ts γ :
    is_txn_committed_ex γ ts -∗
    {{{ own_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__commit #tcoord
    {{{ RET #(); own_tcoord tcoord ts γ }}}.
  Proof.
    (*@ func (tcoord *BackupTxnCoordinator) commit() {                          @*)
    (*@     for _, gcoordloop := range(tcoord.gcoords) {                        @*)
    (*@         gcoord := gcoordloop                                            @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.Commit(tcoord.ts)                                    @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupTxnCoordinator__Finalize tcoord ts γ :
    {{{ own_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__Finalize #tcoord
    {{{ RET #(); own_tcoord tcoord ts γ }}}.
  Proof.
    iIntros (Φ) "Htcoord HΦ".
    wp_rec.

    (*@ func (tcoord *BackupTxnCoordinator) Finalize() {                        @*)
    (*@     status, valid := tcoord.stabilize()                                 @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupTxnCoordinator__stabilize with "Htcoord").
    iIntros (status valid) "[Htcoord Hphase]".
    wp_pures.
    
    (*@     if !valid {                                                         @*)
    (*@         // Skip since a more recent backup txn coordinator is found.    @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct valid eqn:Hvalid; wp_pures; last first.
    { by iApply "HΦ". }

    (*@     if status == tulip.TXN_ABORTED {                                    @*)
    (*@         tcoord.abort()                                                  @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hcond; wp_pures.
    { destruct status eqn:Hstatus; [done | done | ].
      simpl.
      wp_apply (wp_BackupTxnCoordinator__abort with "Hphase Htcoord").
      iIntros "Htcoord".
      wp_pures.
      by iApply "HΦ".
    }

    (*@     // Possible @status: TXN_PREPARED and TXN_COMMITTED. Resolve the prophecy @*)
    (*@     // variable if @status == TXN_PREPARED.                             @*)
    (*@     tcoord.resolve(status)                                              @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupTxnCoordinator__resolve with "Htcoord").
    { by destruct status. }
    iIntros "[Htcoord #Hcmted]".

    (*@     tcoord.commit()                                                     @*)
    (*@ }                                                                       @*)
    wp_apply (wp_BackupTxnCoordinator__commit with "Hcmted Htcoord").
    iIntros "Htcoord".
    wp_pures.
    by iApply "HΦ".
  Qed.

End repr.
