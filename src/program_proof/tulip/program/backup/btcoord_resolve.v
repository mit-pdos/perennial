From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import btcoord_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_mergeKVMap (mwP mrP : loc) q (mw mr : dbmap) :
    {{{ own_map mwP (DfracOwn 1) mw ∗ own_map mrP q mr }}}
      mergeKVMap #mwP #mrP
    {{{ RET #(); own_map mwP (DfracOwn 1) (mr ∪ mw) ∗ own_map mrP q mr }}}.
  Proof.
    (*@ func mergeKVMap(mw, mr tulip.KVMap) {                                   @*)
    (*@     for k, v := range(mr) {                                             @*)
    (*@         mw[k] = v                                                       @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupTxnCoordinator__mergeWrites (tcoord : loc) ts γ :
    {{{ own_backup_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__mergeWrites #tcoord
    {{{ (wrsP : loc) (valid : bool), RET (#wrsP, #valid); True }}}.
  Proof.
    (*@ func (tcoord *BackupTxnCoordinator) mergeWrites() (tulip.KVMap, bool) { @*)
    (*@     var valid bool = true                                               @*)
    (*@     wrs := make(map[string]tulip.Value)                                 @*)
    (*@                                                                         @*)
    (*@     for _, gid := range(tcoord.ptgs) {                                  @*)
    (*@         // TODO: To prove availability of the write set, we'll have to associate @*)
    (*@         // a coordinator-local one-shot ghost variable to @gcoord.pwrsok. The @*)
    (*@         // persistent resource is first given by @gcoord.WaitUntilPrepareDone, @*)
    (*@         // and then is relayed to @gcoord.Prepare and finally to        @*)
    (*@         // @tcoord.stabilize.                                           @*)
    (*@         gcoord := tcoord.gcoords[gid]                                   @*)
    (*@         pwrs, ok := gcoord.GetPwrs()                                    @*)
    (*@         if ok {                                                         @*)
    (*@             mergeKVMap(wrs, pwrs)                                       @*)
    (*@         } else {                                                        @*)
    (*@             valid = false                                               @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     return wrs, valid                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupTxnCoordinator__resolve tcoord status ts γ :
    status ≠ TxnAborted ->
    {{{ own_backup_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__resolve #tcoord #(txnphase_to_u64 status)
    {{{ (ok : bool), RET #ok;
        own_backup_tcoord tcoord ts γ ∗ 
        if ok then is_txn_committed_ex γ ts else True
    }}}.
  Proof.
    (*@ func (tcoord *BackupTxnCoordinator) resolve(status uint64) bool {       @*)
    (*@     if status == tulip.TXN_COMMITTED {                                  @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     wrs, ok := tcoord.mergeWrites()                                     @*)
    (*@     if !ok {                                                            @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     // Logical action: Commit.                                          @*)
    (*@     trusted_proph.ResolveCommit(tcoord.proph, tcoord.ts, wrs)           @*)
    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
