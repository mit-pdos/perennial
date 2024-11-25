From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr gcoord_attached_with gpreparer_repr gpreparer_action.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__NextPrepareAction
    (gcoord : loc) (rid : u64) (tsW : u64) gid γ :
    let ts := uint.nat tsW in
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__NextPrepareAction #gcoord #rid #tsW
    {{{ (action : gppaction) (ok : bool), RET (#(gppaction_to_u64 action), #ok); 
        if ok then safe_gppaction γ ts gid action else True
    }}}.
  Proof.
    iIntros (ts) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) NextPrepareAction(rid uint64, ts uint64) (uint64, bool) { @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@                                                                         @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    do 2 iNamed "Hgcoord".
    wp_apply (wp_GroupCoordinator__attachedWith with "Hgcoord").
    iIntros (ok) "Hgcoord".
    wp_pures.

    (*@     if !gcoord.attachedWith(ts) {                                       @*)
    (*@         gcoord.mu.Unlock()                                              @*)
    (*@         return 0, false                                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct ok; wp_pures; last first.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      (* [GPPFastPrepare] just a placeholder *)
      by iApply ("HΦ" $! GPPFastPrepare).
    }

    (*@     action := gcoord.gpp.action(rid)                                    @*)
    (*@                                                                         @*)
    iNamed "Hgcoord". iNamed "Hgpp".
    wp_loadField.
    wp_apply (wp_GroupPreparer__action with "Hgpp").
    iIntros (action) "[Hgpp #Hsafea]".
    wp_pures.

    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked ∗". }

    (*@     return action, true                                                 @*)
    (*@ }                                                                       @*)
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
