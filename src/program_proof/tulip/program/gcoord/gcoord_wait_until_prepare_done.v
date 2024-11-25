From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr gcoord_attached_with
  gpreparer_repr gpreparer_ready gpreparer_get_phase.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__WaitUntilPrepareDone
    (gcoord : loc) (tsW : u64) gid γ :
    let ts := uint.nat tsW in
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__WaitUntilPrepareDone #gcoord #tsW
    {{{ (tphase : txnphase) (valid : bool), RET (#(txnphase_to_u64 tphase), #valid); 
        if valid then safe_group_txnphase γ ts gid tphase else True
    }}}.
  Proof.
    iIntros (ts) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) WaitUntilPrepareDone(ts uint64) (uint64, bool) { @*)
    (*@     var phase uint64                                                    @*)
    (*@     var valid bool                                                      @*)
    (*@                                                                         @*)
    wp_apply wp_ref_of_zero; first done.
    iIntros (phaseP) "HphaseP".
    wp_apply wp_ref_of_zero; first done.
    iIntros (validP) "HvalidP".

    (*@     gcoord.mu.Lock()                                                    @*)
    (*@                                                                         @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    wp_pures.

    (*@     for {                                                               @*)
    (*@                                                                         @*)
    set P := (λ (cont : bool), ∃ (pphase : gppphase) (valid : bool),
      "Hgcoord" ∷ own_gcoord gcoord addrm gid γ ∗
      "HphaseP" ∷ phaseP ↦[uint64T] #(gppphase_to_u64 pphase) ∗
      "HvalidP" ∷ validP ↦[boolT] #valid ∗
      "Hlocked" ∷ locked #muP ∗
      "#Hsafep" ∷ (if (negb cont) && valid
                   then safe_gpreparer_phase γ ts gid pphase ∗ ⌜gpp_ready pphase⌝
                   else True))%I.
    wp_apply (wp_forBreak P with "[] [Hgcoord HphaseP HvalidP Hlocked]"); last first; first 1 last.
    { iFrame. by iExists GPPValidating. }
    { clear Φ.

      (*@         if !gcoord.attachedWith(ts) {                                   @*)
      (*@             valid = false                                               @*)
      (*@             break                                                       @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      iIntros (Φ) "!> HP HΦ".
      iNamed "HP".
      iDestruct"Hgcoord" as (tscur) "Hgcoord".
      do 2 iNamed "Hgcoord".
      wp_apply (wp_GroupCoordinator__attachedWith with "Hgcoord").
      iIntros (attached) "Hgcoord".
      wp_pures.
      destruct attached; wp_pures; last first.
      { wp_store. iApply "HΦ". by iFrame. }

      (*@         ready := gcoord.gpp.ready()                                     @*)
      (*@         if ready {                                                      @*)
      (*@             phase = gcoord.gpp.getPhase()                               @*)
      (*@             valid = true                                                @*)
      (*@             break                                                       @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      iNamed "Hgcoord". do 2 iNamed "Hgpp".
      wp_loadField.
      wp_apply (wp_GroupPreparer__ready_external with "Hgpp").
      iIntros "Hgpp".
      case_bool_decide; wp_pures.
      { wp_loadField.
        wp_apply (wp_GroupPreparer__getPhase with "Hgpp").
        iIntros "[Hgpp #Hsafegpp]".
        do 2 wp_store.
        iApply "HΦ".
        by iFrame "∗ # %".
      }

      (*@         gcoord.cv.Wait()                                                @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_loadField.
      wp_apply (wp_Cond__Wait with "[-HΦ HphaseP HvalidP]").
      { by iFrame "Hcv Hlock Hlocked ∗ # %". }
      iIntros "[Hlocked Hgcoord]".
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }
    subst P. iNamed 1. simpl.

    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ HphaseP HvalidP]").
    { by iFrame "Hlock Hlocked Hgcoord". }

    (*@     if !valid {                                                         @*)
    (*@         // TXN_PREPARED here is just a placeholder.                     @*)
    (*@         return tulip.TXN_PREPARED, false                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_load. wp_pures.
    destruct valid; wp_pures; last first.
    { by iApply ("HΦ" $! TxnPrepared). }
    iDestruct "Hsafep" as "[Hsafep %Hready]".

    (*@     if phase == GPP_COMMITTED {                                         @*)
    (*@         return tulip.TXN_COMMITTED, true                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_load. wp_pures.
    case_bool_decide; wp_pures.
    { iApply ("HΦ" $! TxnCommitted). by destruct pphase. }

    (*@     if phase == GPP_ABORTED {                                           @*)
    (*@         return tulip.TXN_ABORTED, true                                  @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_load. wp_pures.
    case_bool_decide; wp_pures.
    { iApply ("HΦ" $! TxnAborted). by destruct pphase. }

    (*@     return tulip.TXN_PREPARED, true                                     @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! TxnPrepared). by destruct pphase.
  Qed.

End program.
