From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gcoord_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__RegisterFinalization (gcoord : loc) (tsW : u64) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__RegisterFinalization #gcoord #tsW
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) RegisterFinalization(ts uint64) {       @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     gcoord.tsfinals[ts] = true                                          @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    do 3 iNamed "Hgcoord". iNamed "Hgfl".
    wp_loadField.
    wp_apply (wp_MapInsert with "Htsfinals"); first done.
    iIntros "Htsfinals".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked Hts Hgrd Hgpp Hcomm ∗ %". }
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
