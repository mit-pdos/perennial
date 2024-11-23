From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gcoord_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__processFinalizationResult
    (gcoord : loc) (ts : u64) (res : u64) rids :
    {{{ own_gcoord_finalizer gcoord rids }}}
      GroupCoordinator__processFinalizationResult #gcoord #ts #res
    {{{ RET #(); own_gcoord_finalizer gcoord rids }}}.
  Proof.
    iIntros (Φ) "Hgcoord HΦ".
    wp_rec. wp_pures.

    (*@ func (gcoord *GroupCoordinator) processFinalizationResult(ts uint64, res uint64) { @*)
    (*@     if res == tulip.REPLICA_WRONG_LEADER {                              @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@     delete(gcoord.tsfinals, ts)                                         @*)
    (*@ }                                                                       @*)
    case_bool_decide as Hwrong; wp_pures.
    { by iApply "HΦ". }
    iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_MapDelete with "Htsfinals").
    iIntros "Htsfinals".
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ %".
  Qed.

End program.
