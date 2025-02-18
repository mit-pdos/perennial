From Perennial.program_proof.tulip.invariance Require Import read.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr gcoord_attached_with greader_read.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__WaitUntilValueReady
    (gcoord : loc) (tsW : u64) (key : byte_string) gid γ :
    let ts := uint.nat tsW in
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__WaitUntilValueReady #gcoord #tsW #(LitString key)
    {{{ (value : dbval) (valid : bool), RET (dbval_to_val value, #valid); 
        if valid then fast_or_quorum_read γ key ts value else True
    }}}.
  Proof.
    iIntros (ts) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) WaitUntilValueReady(ts uint64, key string) (tulip.Value, bool) { @*)
    (*@     var value tulip.Value                                               @*)
    (*@     var valid bool                                                      @*)
    (*@                                                                         @*)
    wp_apply wp_ref_of_zero; first done.
    iIntros (valueP) "HvalueP".
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
    set P := (λ (cont : bool), ∃ (value : dbval) (valid : bool),
      "Hgcoord" ∷ own_gcoord gcoord addrm gid γ ∗
      "HvalueP" ∷ valueP ↦[boolT * (stringT * unitT)%ht] dbval_to_val value ∗
      "HvalidP" ∷ validP ↦[boolT] #valid ∗
      "Hlocked" ∷ locked #muP ∗
      "#Hread"  ∷ if (negb cont) && valid then fast_or_quorum_read γ key ts value else True)%I.
    wp_apply (wp_forBreak P with "[] [Hgcoord HvalueP HvalidP Hlocked]"); last first; first 1 last.
    { iFrame. by iExists None. }
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

      (*@         v, ok := gcoord.grd.read(key)                                   @*)
      (*@         if ok {                                                         @*)
      (*@             value = v                                                   @*)
      (*@             valid = true                                                @*)
      (*@             break                                                       @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      iNamed "Hgcoord". iNamed "Hgrd".
      wp_loadField.
      wp_apply (wp_GroupReader__read with "Hgrd").
      iIntros (v ok) "[Hgrd #Hreadv]".
      wp_pures.
      destruct ok; wp_pures.
      { wp_apply (wp_StoreAt with "HvalueP").
        { by destruct v; auto. }
        iIntros "HvalueP".
        wp_store.
        iApply "HΦ".
        by iFrame "∗ #".
      }
    
      (*@         gcoord.cv.Wait()                                                @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_loadField.
      wp_apply (wp_Cond__Wait with "[-HΦ HvalueP HvalidP]").
      { by iFrame "Hcv Hlock Hlocked ∗ # %". }
      iIntros "[Hlocked Hgcoord]".
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }
    subst P. iNamed 1.

    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ HvalueP HvalidP]").
    { by iFrame "Hlock Hlocked Hgcoord". }

    (*@     return value, valid                                                 @*)
    (*@ }                                                                       @*)
    do 2 wp_load.
    wp_pures.
    iApply "HΦ".
    by destruct valid.
  Qed.

End program.
