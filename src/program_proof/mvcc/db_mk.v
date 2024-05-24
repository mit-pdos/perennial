From Perennial.program_proof.mvcc Require Import
     txn_prelude db_repr txnsite_repr
     proph_proof index_proof tid_proof txnsite_mk.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem wp_MkDB :
  {{{ True }}}
    MkDB #()
  {{{ (γ : mvcc_names) (db : loc), RET #db;
      is_db db γ ∗
      dbmap_ptstos γ 1 (gset_to_gmap Nil keys_all)
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.

  (* Allocate ghost states. *)
  iMod mvcc_ghost_alloc as (γ) "H".
  iDestruct "H" as "(Hphys & Hphys' & Hlogi & Hts & Hsids & H)".
  iDestruct "H" as "(Hnca & Hfa & Hfci & Hfcc & Hcmt & Hm & Hpts & Hgentid & H)".
  iDestruct "H" as "(HactiveAuths & HactiveAuths' & HminAuths)".
  iMod (init_GenTID with "Hgentid") as "#Hgentid".

  (*@ func MkDB() *DB {                                                       @*)
  (*@     proph := machine.NewProph()                                         @*)
  (*@                                                                         @*)
  wp_apply (wp_NewProphActions γ).
  iIntros (p acs) "Hproph".

  (*@     db := &DB { proph : proph }                                         @*)
  (*@     db.latch = new(cfmutex.CFMutex)                                     @*)
  (*@     db.sites = make([]*txnsite.TxnSite, config.N_TXN_SITES)             @*)
  (*@                                                                         @*)
  wp_apply (wp_allocStruct); first auto 10.
  iIntros (db) "Hdb".
  iDestruct (struct_fields_split with "Hdb") as "Hdb".
  iNamed "Hdb".
  (*simpl.*)
  wp_pures.
  wp_apply (wp_new_free_lock).
  iIntros (latch) "Hfree".
  wp_storeField.
  wp_apply (wp_new_slice); first done.
  iIntros (sites) "HsitesL".
  wp_storeField.

  (*@     // Call this once to establish invariants.                          @*)
  (*@     tid.GenTID(0)                                                       @*)
  (*@                                                                         @*)
  iDestruct (big_sepL_lookup_acc _ _ 0 with "Hsids") as "[Hsid0 Hsids]".
  { done. }
  (**
   * Call `GenTID` once to get [ts_auth γ 1] and [ts_lb γ 1].
   * Note that we own [ts_auth] exclusively, not from some invariant.
   *)
  wp_apply (wp_GenTID with "Hgentid Hsid0").
  iApply ncfupd_mask_intro; first solve_ndisj.
  iIntros "Hclose".
  iExists _. iFrame "Hts".
  iIntros "%ts (Hts & %Hgz)".
  iMod "Hclose". iModIntro.
  (* Don't care about its return value. *)
  iIntros (tid) "[_ Hsid0]". iDestruct ("Hsids" with "Hsid0") as "Hsids".
  wp_pures.
  iDestruct (ts_witness with "Hts") as "#Htslb".

  (* Establish the GC invariant. *)
  iMod (inv_alloc mvccNGC _ (mvcc_inv_gc_def γ) with "[HactiveAuths' HminAuths]") as "#Hinvgc".
  { iNext. unfold mvcc_inv_gc_def.
    iDestruct (big_sepL_sep_2 with "HactiveAuths' HminAuths") as "HinvgcO".
    iApply (big_sepL_impl with "HinvgcO").
    iModIntro.
    iIntros (i sid) "%Hlookup [HactiveAuths' HminAuths]".
    iExists _, _, 0%nat.
    iFrame "∗".
    iSplit.
    { iApply (ts_lb_weaken with "Htslb"). lia. }
    iPureIntro.
    split; first done.
    apply set_Forall_union; last done.
    rewrite set_Forall_singleton. lia.
  }

  (* Establish the SST invariants. *)
  iMod (inv_alloc mvccNSST _ (mvcc_inv_sst_def γ p) with
         "[Hts Hm Hproph Hphys Hlogi Hcmt Hnca Hfa Hfci Hfcc]") as "#Hinv".
  { iNext. unfold mvcc_inv_sst_def.
    do 7 iExists _. iExists [], _.
    iFrame "Hts Hm Hproph".
    iSplitL "Hphys Hlogi"; last first.
    { (* Prove prophecy-related invariants. *)
      iSplitL "Hcmt"; first by iFrame.
      iSplitL "Hnca"; first by iFrame.
      iSplitL "Hfa"; first by iFrame.
      iSplitL "Hfci"; first by iFrame.
      iSplitL "Hfcc"; first by iFrame.
      iPureIntro. unfold fc_tids_unique.
      rewrite elements_empty. simpl.
      apply NoDup_nil_2.
    }
    { (* Prove per-key invariants. *)
      iDestruct (big_sepS_sep_2 with "Hphys Hlogi") as "Hpl".
      iApply (big_sepS_mono with "Hpl").
      iIntros (k Helem) "[Hphys Hlogi]".
      do 2 iExists _.
      iFrame.
      iPureIntro.
      split.
      { (* Prove [tuple_mods_rel]. *)
        unfold tuple_mods_rel.
        replace (per_tuple_mods ∅ k) with (∅ : gset (nat * dbval)); last set_solver.
        exists [], Nil.
        split; first done.
        split; first done.
        split.
        { rewrite elements_empty. simpl. apply NoDup_nil_2. }
        split; done.
      }
      split; first by unfold ptuple_past_rel.
      split.
      { simpl. symmetry. apply lookup_gset_to_gmap_Some; done. }
      { simpl. lia. }
    }
  }

  (*@     for i := uint64(0); i < config.N_TXN_SITES; i++ {                   @*)
  (*@         site := txnsite.MkTxnSite(i)                                    @*)
  (*@         db.sites[i] = site                                              @*)
  (*@     }                                                                   @*)
  (*@     db.idx = index.MkIndex()                                            @*)
  (*@                                                                         @*)
  wp_apply (wp_ref_to); first auto.
  iIntros (iRef) "HiRef".
  wp_pures.
  iDestruct (own_slice_to_small with "HsitesL") as "HsitesS".
  set P := λ (n : u64), (∃ sitesL,
    "HsitesS" ∷ own_slice_small sites ptrT (DfracOwn 1) (to_val <$> sitesL) ∗
    "%Hlength" ∷ (⌜Z.of_nat (length sitesL) = N_TXN_SITES⌝) ∗
    "#HsitesRP" ∷ ([∗ list] sid ↦ site ∈ (take (uint.nat n) sitesL), is_txnsite site sid γ) ∗
    "Hsites" ∷ (db ↦[DB :: "sites"] (to_val sites)) ∗
    "HactiveAuths" ∷ ([∗ list] sid ∈ (drop (uint.nat n) sids_all), site_active_tids_half_auth γ sid ∅) ∗
    "Hsids" ∷ ([∗ list] sid ∈ (drop (uint.nat n) sids_all), sid_own γ sid))%I.
  wp_apply (wp_forUpto P _ _ (W64 0) (W64 N_TXN_SITES) with "[] [HsitesS sites $HiRef HactiveAuths Hsids]"); first done.
  { clear Φ latch.
    iIntros (i Φ) "!> (Hloop & HiRef & %Hbound) HΦ".
    iNamed "Hloop".
    wp_pures.
    wp_load.
    rewrite (drop_S _ i); last first.
    { unfold sids_all, N_TXN_SITES in *.
      rewrite list_lookup_fmap.
      rewrite lookup_seqZ_lt; last word.
      simpl. f_equal. word.
    }
    iDestruct (big_sepL_cons with "HactiveAuths") as "[HactiveAuth HactiveAuths]".
    iDestruct (big_sepL_cons with "Hsids") as "[Hsid Hsids]".
    wp_apply (wp_MkTxnSite with "[HactiveAuth $Hsid]"); first by iFrame "∗#".
    iIntros (site) "HsiteRP".
    wp_pures.
    
    replace (uint.Z 32) with (Z.of_nat (length sitesL)) in Hbound.
    unfold N_TXN_SITES in *.
    wp_load.
    wp_loadField.
    wp_apply (wp_SliceSet with "[$HsitesS]").
    { iPureIntro.
      split; last auto.
      apply lookup_lt_is_Some.
      rewrite fmap_length.
      word.
    }
    iIntros "HsitesS".
    wp_pures.
    iApply "HΦ".
    iFrame.

    iModIntro.
    rewrite -list_fmap_insert.
    iExists _.
    iFrame.
    rewrite insert_length.
    iSplit; first done.
    replace (uint.nat (word.add i 1)) with (S (uint.nat i)); last word.
    iFrame.
    rewrite (take_S_r _ _ site); last first.
    { apply list_lookup_insert. word. }
    iApply (big_sepL_app).
    iSplitL "HsitesRP".
    { by rewrite take_insert; last auto. }
    iApply (big_sepL_singleton).
    unfold is_txnsite.
    rewrite take_length_le; last first.
    { rewrite insert_length. word. }
    (* Set Printing Coercions. *)
    replace (W64 _) with i by word.
    eauto 10 with iFrame.
  }
  { iExists (replicate 32 null).
    auto with iFrame.
  }
  iIntros "[Hloop HiRef]".
  iNamed "Hloop".
  wp_pures.
  
  (*@     mgr.idx = index.MkIndex()                                           @*)
  (*@                                                                         @*)
  wp_apply (wp_MkIndex γ with "Hinvgc Hinv Hphys'").
  iIntros (idx) "#HidxRP".
  wp_storeField.

  (*@     return db                                                           @*)
  (*@ }                                                                       @*)
  iApply "HΦ".
  rewrite /is_db.
  iMod (readonly_alloc_1 with "latch") as "#Hlatch".
  iMod (alloc_lock mvccN _ latch (own_db db) with "[$Hfree] [sid]") as "#Hlock".
  { eauto with iFrame. }
  iMod (readonly_alloc_1 with "idx") as "#Hidx".
  iMod (readonly_alloc_1 with "proph") as "#Hp".
  iMod (readonly_alloc_1 with "Hsites") as "#Hsites".
  iMod (readonly_alloc_1 with "HsitesS") as "#HsitesS".
  replace (uint.nat (W64 N_TXN_SITES)) with (length sitesL); last first.
  { unfold N_TXN_SITES in *. word. }
  iFrame "Hpts".
  rewrite firstn_all.
  by iFrame "HidxRP # %".
Qed.

End program.
