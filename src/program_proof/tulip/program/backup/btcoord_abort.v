From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  btcoord_repr bgcoord_repr bgcoord_abort.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupTxnCoordinator__abort tcoord ts γ :
    is_txn_aborted γ ts -∗
    {{{ own_backup_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__abort #tcoord
    {{{ RET #(); own_backup_tcoord tcoord ts γ }}}.
  Proof.
    iIntros "#Habort" (Φ) "!> Htcoord HΦ".
    wp_rec.

    (*@ func (tcoord *BackupTxnCoordinator) abort() {                           @*)
    (*@     for _, gcoordloop := range(tcoord.gcoords) {                        @*)
    (*@         gcoord := gcoordloop                                            @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.Abort(tcoord.ts)                                     @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iNamed "Htcoord". iNamed "Hts". iNamed "Hgcoords".
    do 2 wp_loadField.
    wp_apply (wp_MapIter_fold _ _ _ (λ _, True)%I with "Hgcoords []").
    { done. }
    { clear Φ.
      iIntros (mx gid gcoord Φ) "!> [_ %Hmx] HΦ".
      wp_pures.
      wp_apply wp_fork.
      { iDestruct (big_sepM_lookup with "Hgcoordsabs") as "Hgcoord".
        { destruct Hmx as [_ Hgcoord]. apply Hgcoord. }
        wp_apply (wp_BackupGroupCoordinator__Abort).
        { rewrite HtsW. iNamed "Hwrs". by iFrame "#". }
        { by rewrite HtsW. }
        done.
      }
      by iApply "HΦ".
    }
    iIntros "[Hgcoords _]".
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

End program.
