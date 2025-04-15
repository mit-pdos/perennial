From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import btcoord_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupTxnCoordinator__resolve tcoord status ts γ :
    status ≠ TxnAborted ->
    {{{ own_backup_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__resolve #tcoord #(txnphase_to_u64 status)
    {{{ RET #(); own_backup_tcoord tcoord ts γ ∗ is_txn_committed_ex γ ts }}}.
  Proof.
    (*@ func (tcoord *BackupTxnCoordinator) resolve(status uint64) {            @*)
    (*@     if status == tulip.TXN_PREPARED {                                   @*)
    (*@         // Logical action: Commit.                                      @*)
    (*@         trusted_proph.ResolveCommit(tcoord.proph, tcoord.ts, tcoord.mergeWrites()) @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
