From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgcoord_repr bgpreparer_repr mk_bgpreparer.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_mkBackupGroupCoordinator
    (addrmP : loc) (cid : coordid) (tsW rkW : u64) (addrm : gmap u64 chan) gid γ :
    let ts := uint.nat tsW in
    let rk := uint.nat rkW in
    (1 < rk)%nat ->
    gid ∈ gids_all ->
    dom addrm = rids_all ->
    own_map addrmP DfracDiscarded addrm -∗
    know_tulip_inv γ -∗
    know_tulip_network_inv γ gid addrm -∗
    {{{ own_replica_backup_token γ cid.1 cid.2 ts rk gid }}}
      mkBackupGroupCoordinator #addrmP (coordid_to_val cid) #tsW #rkW
    {{{ (gcoord : loc), RET #gcoord; 
        is_backup_gcoord_with_addrm gcoord addrm rk ts gid γ
    }}}.
  Proof.
    iIntros (ts rk Hrk Hgid Hdomaddrm) "#Haddrm #Hinv #Hinvnet".
    iIntros (Φ) "!> Htoken HΦ".
    wp_rec.

    (*@ func mkBackupGroupCoordinator(addrm map[uint64]grove_ffi.Address, cid tulip.CoordID) *BackupGroupCoordinator { @*)
    (*@     mu := new(sync.Mutex)                                               @*)
    (*@     cv := sync.NewCond(mu)                                              @*)
    (*@     nrps := uint64(len(addrm))                                          @*)
    (*@                                                                         @*)
    wp_apply wp_new_free_lock.
    iIntros (muP) "Hfree".
    wp_apply (wp_newCond' with "Hfree").
    iIntros (cvP) "[Hfree #Hcv]".
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
                 "%Hrps" ∷ ⌜list_to_set l = dom mx⌝ ∗
                 "%Hnd"  ∷ ⌜NoDup l⌝)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "Haddrm [$Hrps $HrpsP]").
    { by rewrite NoDup_nil. }
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
      split; first set_solver.
      apply NoDup_snoc; last done.
      destruct Hrid as [Hnotin _].
      apply not_elem_of_dom in Hnotin.
      rewrite -Hrps in Hnotin.
      set_solver.
    }
    iIntros "[_ HP]".
    iNamed "HP".

    (*@     gcoord := &BackupGroupCoordinator{                                  @*)
    (*@         cid       : cid,                                                @*)
    (*@         rps       : rps,                                                @*)
    (*@         addrm     : addrm,                                              @*)
    (*@         mu        : mu,                                                 @*)
    (*@         cv        : cv,                                                 @*)
    (*@         idxleader : 0,                                                  @*)
    (*@         gpp       : mkBackupGroupPreparer(nrps),                        @*)
    (*@         conns     : make(map[uint64]grove_ffi.Connection),              @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_load.
    wp_apply (wp_mkBackupGroupPreparer with "Htoken").
    { rewrite -Hdomaddrm size_dom. word. }
    iIntros (gpp) "Hgpp".
    wp_apply (map.wp_NewMap).
    iIntros (conns) "Hconns".
    rewrite {1}/zero_val /=.
    wp_pures.
    wp_apply (wp_allocStruct).
    { by auto 15. }
    iIntros (gcoord) "Hgcoord".
    iDestruct (struct_fields_split with "Hgcoord") as "Hgcoord".
    iNamed "Hgcoord".
    wp_pures.

    (*@     return gcoord                                                       @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iAssert (own_backup_gcoord_gpreparer gcoord rk ts cid gid γ)%I
      with "[$gpp $Hgpp]" as "Hgpp".
    iAssert (own_backup_gcoord_leader gcoord (dom addrm))%I with "[$idxleader]" as "Hleader".
    { iPureIntro. rewrite Hdomaddrm size_rids_all. word. }
    iAssert (own_backup_gcoord_comm gcoord addrm gid γ)%I with "[$conns Hconns]" as "Hcomm".
    { iExists ∅.
      rewrite fmap_empty big_sepM_empty.
      by iFrame.
    }
    iAssert (own_backup_gcoord gcoord addrm rk ts cid gid γ)%I
      with "[$Hgpp $Hleader $Hcomm]" as "Hgcoord".
    iMod (alloc_lock _ _ _ (own_backup_gcoord gcoord addrm rk ts cid gid γ)
           with "Hfree [$Hgcoord]") as "#Hlock".
    iMod (readonly_alloc_1 with "mu") as "#HmuP".
    iMod (readonly_alloc_1 with "cv") as "#HcvP".
    iClear "HrpsP".
    iMod (readonly_alloc_1 with "rps") as "#HrpsP".
    iMod (readonly_alloc_1 with "addrm") as "#HaddrmP".
    iDestruct (own_slice_to_small with "Hrps") as "Hrps".
    iMod (readonly_alloc_1 with "Hrps") as "#Hrps".
    iMod (readonly_alloc_1 with "cid") as "#Hcid".
    iMod (readonly_alloc_1 with "ts") as "#Hts".
    iMod (readonly_alloc_1 with "rank") as "#Hrank".
    iFrame "# %".
    iPureIntro.
    by rewrite Hrps.
  Qed.
  
End program.
