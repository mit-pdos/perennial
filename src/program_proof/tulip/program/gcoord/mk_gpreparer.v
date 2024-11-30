From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gpreparer_repr .
  
Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_mkGroupPreparer (nrps : u64) gid γ :
    uint.nat nrps = size rids_all ->
    {{{ True }}}
      mkGroupPreparer #nrps
    {{{ (gpp : loc), RET #gpp; own_gpreparer gpp O gid γ }}}.
  Proof.
    iIntros (Hnrps Φ) "_ HΦ".
    wp_rec.

    (*@ func mkGroupPreparer(nrps uint64) *GroupPreparer {                      @*)
    (*@     gpp := &GroupPreparer{ nrps : nrps }                                @*)
    (*@     gpp.phase = GPP_WAITING                                             @*)
    (*@     gpp.frespm = make(map[uint64]bool)                                  @*)
    (*@     gpp.vdm = make(map[uint64]bool)                                     @*)
    (*@                                                                         @*)
    wp_apply (wp_allocStruct).
    { by auto 10. }
    iIntros (gpp) "Hgpp".
    iDestruct (struct_fields_split with "Hgpp") as "Hgpp".
    iNamed "Hgpp".
    wp_storeField.
    wp_apply (wp_NewMap u64 bool).
    iIntros (frespmP) "Hfrespm".
    wp_storeField.
    wp_apply (wp_NewMap u64 bool).
    iIntros (vdmP) "Hvdm".
    wp_storeField.
    
    (*@     return gpp                                                          @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iFrame "nrps phase frespm vdm srespm ∗ %".
    iExists GPPWaiting.
    iModIntro.
    iSplit; first done.
    iSplit.
    { iSplit; last done. by iApply big_sepM_empty. }
    iSplit.
    { iSplit; last done. by rewrite /validation_responses dom_empty_L big_sepS_empty. }
    iSplit.
    { iExists ∅. done. }
    by iFrame.
  Qed.

End program.
