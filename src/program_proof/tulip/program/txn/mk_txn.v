From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import txn_repr.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr start.
  
Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_mkTxn
    (sid : u64) (gaddrmPP : loc) (gaddrmP : gmap u64 loc)
    (gaddrm : gmap u64 (gmap u64 chan)) (proph : proph_id) γ :
    uint.Z sid < zN_TXN_SITES →
    dom gaddrm = gids_all ->
    map_Forall (λ _ addrm, dom addrm = rids_all) gaddrm ->
    own_map gaddrmPP DfracDiscarded gaddrmP -∗
    ([∗ map] addrmP; addrm ∈ gaddrmP; gaddrm, own_map addrmP DfracDiscarded addrm) -∗
    have_gentid γ -∗
    know_tulip_inv_with_proph γ proph -∗
    ([∗ map] gid ↦ addrm ∈ gaddrm, know_tulip_network_inv γ gid addrm) -∗
    {{{ own_sid γ sid }}}
      mkTxn #sid #gaddrmPP #proph
    {{{ (txn : loc), RET #txn; own_txn_uninit txn γ }}}.
  Proof.
    iIntros (Hlt Hgid Hrids) "#HgaddrmP #Hgaddrm #Hgentid #Hinv #Hinvnets".
    iIntros (Φ) "!> Hown_sid HΦ".
    wp_rec.

    (*@ func mkTxn(sid uint64, gaddrm map[uint64]map[uint64]grove_ffi.Address, proph primitive.ProphId) *Txn { @*)
    (*@     txn := &Txn{ sid : sid, proph : proph }                             @*)
    (*@                                                                         @*)
    wp_apply (wp_allocStruct).
    { by auto 10. }
    iIntros (txn) "Htxn".
    iDestruct (struct_fields_split with "Htxn") as "Htxn".
    iNamed "Htxn".

    (*@     wrs := make(map[uint64]map[string]tulip.Value)                      @*)
    (*@     for gid := range(gaddrm) {                                          @*)
    (*@         wrs[gid] = make(map[string]tulip.Value)                         @*)
    (*@     }                                                                   @*)
    (*@     txn.wrs = wrs                                                       @*)
    (*@     txn.wrsp = make(map[string]tulip.Value)                             @*)
    (*@                                                                         @*)
    wp_apply wp_NewMap.
    iIntros (wrsPP) "HwrsP".
    set P := (λ (mx : gmap u64 loc),
                let em := gset_to_gmap (∅ : dbmap) (dom mx) in
                ∃ (wrsP : gmap u64 loc),
                  "HwrsP" ∷ own_map wrsPP (DfracOwn 1) wrsP ∗
                  "Hwrs"  ∷ ([∗ map] p; m ∈ wrsP; em, own_map p (DfracOwn 1) m))%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "HgaddrmP [HwrsP]").
    { subst P. simpl.
      rewrite dom_empty_L gset_to_gmap_empty.
      iFrame.
      by iApply big_sepM2_empty.
    }
    { clear Φ.
      iIntros (m gid pwrsP Φ) "!> [HP [%Hnone %Hsome]] HΦ".
      iNamed "HP".
      wp_pures.
      wp_apply wp_NewMap.
      iIntros (empP) "HempP".
      wp_apply (wp_MapInsert with "HwrsP"); first by auto.
      iIntros "HwrsP".
      iApply "HΦ".
      subst P. simpl.
      iFrame.
      rewrite dom_insert_L gset_to_gmap_union_singleton.
      iApply (big_sepM2_insert_2 with "[HempP] Hwrs"); first iFrame.
    }
    iIntros "[_ HP]".
    subst P. simpl.
    iNamed "HP".
    wp_storeField.
    wp_apply (wp_NewMap dbkey dbval).
    iIntros (wrspP) "Hwrsp".
    wp_storeField.

    (*@     gcoords := make(map[uint64]*gcoord.GroupCoordinator)                @*)
    (*@     for gid, addrm := range(gaddrm) {                                   @*)
    (*@         gcoords[gid] = gcoord.Start(addrm)                              @*)
    (*@     }                                                                   @*)
    (*@     txn.gcoords = gcoords                                               @*)
    (*@                                                                         @*)
    iDestruct (big_sepM2_dom with "Hgaddrm") as %Hdomgaddrm.
    wp_apply (wp_NewMap u64 loc).
    iIntros (gcoordsPP) "HgcoordsP".
    set P := (λ (mx : gmap u64 loc), ∃ (gcoordsP : gmap u64 loc),
                 "HgcoordsP" ∷ own_map gcoordsPP (DfracOwn 1) gcoordsP ∗
                 "#Hgcoords" ∷ ([∗ map] gid ↦ gcoord ∈ gcoordsP, is_gcoord gcoord gid γ) ∗
                 "%Hdom"     ∷ ⌜dom gcoordsP = dom mx⌝)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "HgaddrmP [HgcoordsP]").
    { subst P. simpl.
      iFrame.
      by rewrite big_sepM_empty.
    }
    { clear Φ.
      iIntros (m gid p Φ) "!> [HP [_ %Hp]] HΦ".
      iNamed "HP".
      wp_pures.
      assert (is_Some (gaddrm !! gid)) as [addrm Haddrm].
      { by rewrite -elem_of_dom -Hdomgaddrm elem_of_dom. }
      wp_apply wp_Start.
      { apply elem_of_dom_2 in Hp. by rewrite Hdomgaddrm Hgid in Hp. }
      { specialize (Hrids _ _ Haddrm). simpl in Hrids. done. }
      { by iApply (big_sepM2_lookup with "Hgaddrm"). }
      { iExists proph. done. }
      { by iApply (big_sepM_lookup with "Hinvnets"). }
      iIntros (gcoord) "#Hgcoord".
      wp_apply (wp_MapInsert with "HgcoordsP"); first done.
      iIntros "HgcoordsP".
      iApply "HΦ".
      iFrame.
      iSplit; first by iApply big_sepM_insert_2.
      iPureIntro.
      by rewrite 2!dom_insert_L Hdom.
    }
    iIntros "[_ HP]".
    iNamed "HP".

    (*@     return txn                                                          @*)
    (*@ }                                                                       @*)
    wp_storeField.
    iApply "HΦ".
    iAssert (own_txn_ts txn O)%I with "[$ts]" as "Hts"; first word.
    iDestruct (big_sepM2_dom with "Hwrs") as %Hdomwrs.
    rewrite dom_gset_to_gmap in Hdomwrs.
    iAssert (own_txn_wrs txn (DfracOwn 1) ∅)%I
      with "[$wrs $wrsp $HwrsP $Hwrs $Hwrsp]" as "Hwrs".
    { iPureIntro.
      split.
      { intros g m Hm.
        by apply lookup_gset_to_gmap_Some in Hm as [_ <-].
      }
      by rewrite Hdomwrs Hdomgaddrm Hgid.
    }
    iAssert (own_txn_ptgs_empty txn)%I with "[ptgs]" as "Hptgs".
    { iExists Slice.nil. by iFrame. }
    iRename "Hgcoords" into "Hgcoordsabs".
    iAssert (own_txn_gcoords txn γ)%I with "[$gcoords $HgcoordsP]" as "Hgcoords".
    { iFrame "#". by rewrite Hdom Hdomgaddrm Hgid. }
    by iFrame "∗ #".
  Qed.

End program.
