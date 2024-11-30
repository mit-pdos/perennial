From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gpreparer_repr greader_repr gcoord_repr.
  
Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupPreparer__reset (gpp : loc) ts gid γ :
    {{{ own_gpreparer_uninit gpp }}}
      GroupPreparer__reset #gpp
    {{{ RET #(); own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) reset() {                                     @*)
    (*@     gpp.phase = GPP_VALIDATING                                          @*)
    (*@     gpp.frespm = make(map[uint64]bool)                                  @*)
    (*@     gpp.vdm = make(map[uint64]bool)                                     @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp".
    wp_storeField.
    wp_apply (wp_NewMap u64 bool).
    iIntros (frespmP') "Hfrespm".
    wp_storeField.
    wp_apply (wp_NewMap u64 bool).
    iIntros (vdmP') "Hvdm".
    wp_storeField.
    iApply "HΦ".
    iFrame "HnrpsP HphaseP HfrespmP HvdmP HsrespmP ∗ %".
    iExists GPPValidating. simpl.
    iModIntro.
    iSplit; first done.
    iSplit.
    { iSplit; last done. by iApply big_sepM_empty. }
    iSplit.
    { iSplit; last done. by rewrite /validation_responses dom_empty_L big_sepS_empty. }
    iSplit.
    { iExists ∅. done. }
    
    rewrite Hnrps.
    simpl.
    iSplit
  Admitted.

  Theorem wp_mkGroupPreparer (nrps : u64) gid γ :
    {{{ True }}}
      mkGroupPreparer #nrps
    {{{ (gpp : loc), RET #gpp; own_gpreparer gpp O gid γ }}}.
  Proof.
    (*@ func mkGroupPreparer(nrps uint64) *GroupPreparer {                      @*)
    (*@     gpp := &GroupPreparer{ nrps : nrps }                                @*)
    (*@     gpp.reset()                                                         @*)
    (*@                                                                         @*)
    (*@     return gpp                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_mkGroupCoordinator (addrmP : loc) (addrm : gmap u64 chan) gid γ :
    own_map addrmP DfracDiscarded addrm -∗
    {{{ True }}}
      mkGroupCoordinator #addrmP
    {{{ (gcoord : loc), RET #gcoord; is_gcoord gcoord gid γ }}}.
  Proof.
    iIntros "#Haddrm" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func mkGroupCoordinator(addrm map[uint64]grove_ffi.Address) *GroupCoordinator { @*)
    (*@     mu := new(sync.Mutex)                                               @*)
    (*@     cv := sync.NewCond(mu)                                              @*)
    (*@     cvrs := sync.NewCond(mu)                                            @*)
    (*@     nrps := uint64(len(addrm))                                          @*)
    (*@                                                                         @*)
    wp_apply wp_new_free_lock.
    iIntros (muP) "Hfree".
    wp_apply (wp_newCond' with "Hfree").
    iIntros (cvP) "[Hfree #Hcv]".
    wp_apply (wp_newCond' with "Hfree").
    iIntros (cvrsP) "[Hfree #Hcvrs]".
    wp_apply (wp_MapLen with "Haddrm").
    iIntros "[%Hnoof _]".

    (*@     var rps = make([]uint64, 0)                                         @*)
    (*@     for rid := range(addrm) {                                           @*)
    (*@         rps = append(rps, rid)                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply wp_NewSlice.
    iIntros (rpsP) "Hrps".
    rewrite uint_nat_W64_0 replicate_0.
    wp_apply wp_ref_to; first done.
    iIntros (rpsPP) "HrpsP".
    set P := (λ (mx : gmap u64 chan), ∃ (rpsP' : Slice.t) (l : list u64),
                 "HrpsP" ∷ rpsPP ↦[slice.T uint64T] rpsP' ∗
                 "Hrps"  ∷ own_slice rpsP' uint64T (DfracOwn 1) l ∗
                 "%Hrps" ∷ ⌜list_to_set l = dom mx⌝)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "Haddrm [$Hrps $HrpsP]").
    { done. }
    { clear Φ.
      iIntros (mx rid c Φ) "!> [HP %Hrid] HΦ".
      iNamed "HP".
      wp_load.
      wp_apply (wp_SliceAppend with "Hrps").
      iIntros (rpsP'') "Hrps".
      wp_store.
      iApply "HΦ".
      iFrame.
      iPureIntro.
      rewrite list_to_set_app_L dom_insert_L Hrps /=.
      set_solver.
    }
    iIntros "[_ HP]".
    iNamed "HP".

    (*@     gcoord := &GroupCoordinator{                                        @*)
    (*@         rps       : rps,                                                @*)
    (*@         addrm     : addrm,                                              @*)
    (*@         mu        : mu,                                                 @*)
    (*@         cv        : cv,                                                 @*)
    (*@         cvrs      : cvrs,                                               @*)
    (*@         idxleader : 0,                                                  @*)
    (*@         grd       : mkGroupReader(nrps),                                @*)
    (*@         gpp       : mkGroupPreparer(nrps),                              @*)
    (*@         tsfinals  : make(map[uint64]bool),                              @*)
    (*@         conns     : make(map[uint64]grove_ffi.Connection),              @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_load.

    (*@     return gcoord                                                       @*)
    (*@ }                                                                       @*)
  Admitted.


End program.
