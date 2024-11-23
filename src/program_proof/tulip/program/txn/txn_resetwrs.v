From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import txn_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Txn__resetwrs (txn : loc) q wrs :
    {{{ own_txn_wrs txn q wrs }}}
      Txn__resetwrs #txn
    {{{ RET #(); own_txn_wrs txn (DfracOwn 1) ∅ }}}.
  Proof.
    iIntros (Φ) "Hwrs HΦ".
    wp_rec.

    (*@ func (txn *Txn) resetwrs() {                                            @*)
    (*@     // Creating a new @wrs is not really necessary, but currently it seems like @*)
    (*@     // there's no easy way to reason modifying a map while iterating over it @*)
    (*@     // (which is a defined behavior in Go).                             @*)
    (*@     wrs := make(map[uint64]map[string]tulip.Value)                      @*)
    (*@     for gid := range(txn.wrs) {                                         @*)
    (*@         wrs[gid] = make(map[string]tulip.Value)                         @*)
    (*@     }                                                                   @*)
    (*@     txn.wrs = wrs                                                       @*)
    (*@     txn.wrsp = make(map[string]tulip.Value)                             @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewMap.
    iIntros (wrsP') "HpwrsmP'".
    do 2 iNamed "Hwrs".
    (* iDestruct (big_sepM2_dom with "Hpwrsm") as %Hdom. *)
    wp_loadField.
    set P := (λ (mx : gmap u64 loc),
      let em := gset_to_gmap (∅ : dbmap) (dom mx) in
      ∃ (pwrsmP' : gmap u64 loc),
        "HpwrsmP'" ∷ own_map wrsP' (DfracOwn 1) pwrsmP' ∗
        "Hpwrsm'"  ∷ ([∗ map] p;m ∈ pwrsmP';em, own_map p (DfracOwn 1) m))%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "HpwrsmP [HpwrsmP']").
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
      wp_apply (wp_MapInsert with "HpwrsmP'"); first by auto.
      iIntros "HpwrsmP'".
      iApply "HΦ".
      subst P. simpl.
      iFrame.
      rewrite dom_insert_L gset_to_gmap_union_singleton.
      iApply (big_sepM2_insert_2 with "[HempP] Hpwrsm'"); first iFrame.
    }
    iIntros "[HpwrsmP HP]".
    subst P. simpl.
    iNamed "HP".
    wp_storeField.
    wp_apply wp_NewMap.
    iIntros (wrspP') "HwrspP'".
    wp_storeField.
    iApply "HΦ".
    iDestruct (big_sepM2_dom with "Hpwrsm'") as %Hdom'.
    iFrame "∗ %".
    iPureIntro.
    split; last first.
    { by rewrite Hdom' dom_gset_to_gmap Hdomwrs. }
    intros g m Hgm.
    rewrite lookup_gset_to_gmap_Some in Hgm.
    destruct Hgm as [_ Hm].
    by rewrite /wrs_group map_filter_empty.
  Qed.

End program.
