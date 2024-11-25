From Perennial.program_proof.tulip.invariance Require Import read.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr greader_responded.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__ValueResponded gcoord (rid : u64) key gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__ValueResponded #gcoord #rid #(LitString key)
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) ValueResponded(rid uint64, key string) bool { @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     done := gcoord.grd.responded(rid, key)                              @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@     return done                                                         @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    do 3 iNamed "Hgcoord". iNamed "Hgrd".
    wp_loadField.
    wp_pures.
    wp_apply (wp_GroupReader__responded with "Hgrd").
    iIntros (responded) "Hgrd".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hlock Hlocked". by iFrame "∗ # %". }
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
