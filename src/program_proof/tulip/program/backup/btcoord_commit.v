From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import btcoord_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupTxnCoordinator__commit tcoord ts γ :
    is_txn_committed_ex γ ts -∗
    {{{ own_backup_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__commit #tcoord
    {{{ RET #(); own_backup_tcoord tcoord ts γ }}}.
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

End program.
