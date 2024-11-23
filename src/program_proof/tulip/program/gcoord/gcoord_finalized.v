From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gcoord_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__Finalized (gcoord : loc) (tsW : u64) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__Finalized #gcoord #tsW
    {{{ (finalized : bool), RET #finalized; True }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) Finalized(ts uint64) bool {             @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     _, ok := gcoord.tsfinals[ts]                                        @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@     return !ok                                                          @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    do 3 iNamed "Hgcoord". iNamed "Hgfl".
    wp_loadField.
    wp_apply (wp_MapGet with "Htsfinals").
    iIntros (v ok) "[%Hok Htsfinals]".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked Hts Hgrd Hgpp Hcomm ∗ %". }
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
