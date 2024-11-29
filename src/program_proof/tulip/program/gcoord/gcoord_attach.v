From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gcoord_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__Attach (gcoord : loc) (ts : u64) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__Attach #gcoord #ts
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) Attach(ts uint64) {                     @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     gcoord.ts = ts                                                      @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    do 3 iNamed "Hgcoord". iNamed "Hts".
    wp_storeField.
  Admitted.

End program.
