From Perennial.program_proof.mvcc Require Import proph_proof txn_common.
(* XXX: Must import in this order because of typed/untyped slices... *)

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.
(*****************************************************************)
(* func MkTxnMgr() *TxnMgr                                       *)
(*****************************************************************)
Theorem wp_MkTxnMgr :
  {{{ True }}}
    MkTxnMgr #()
  {{{ (γ : mvcc_names) (txnmgr : loc), RET #txnmgr; is_txnmgr txnmgr γ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.

  (***********************************************************)
  (* txnMgr := new(TxnMgr)                                   *)
  (* txnMgr.latch = new(sync.Mutex)                          *)
  (* txnMgr.sites = make([]*TxnSite, config.N.TXN_SITES)     *)
  (***********************************************************)
  wp_apply (wp_allocStruct); first auto 10.
  iIntros (txnmgr) "Htxnmgr".
  iDestruct (struct_fields_split with "Htxnmgr") as "Htxnmgr".
  iNamed "Htxnmgr".
  simpl.
  wp_pures.
  wp_apply (wp_new_free_lock).
  iIntros (latch) "Hfree".
  wp_storeField.
  wp_apply (wp_new_slice); first done.
  iIntros (sites) "HsitesL".
  wp_storeField.

  iMod mvcc_ghost_init as (γ) "(Hvchains & Hvchains' & HactiveAuths & HactiveAuths' & HminAuths & HminAuths')".
  (* TODO: allocate inv sst with Hvchains' *)
  iMod (inv_alloc mvccNGC _ (mvcc_inv_gc_def γ) with "[HactiveAuths' HminAuths']") as "#Hinvgc".
  { iNext. unfold mvcc_inv_gc_def.
    iDestruct (big_sepL_sep_2 with "HactiveAuths' HminAuths'") as "HinvgcO".
    iApply big_sepL_mono; last iAccu.
    iIntros (i sid) "%Hlookup [HactiveAuths' HminAuths']".
    iExists ∅, (U64 0).
    by iFrame.
  }

  (***********************************************************)
  (* for i := uint64(0); i < config.N.TXN_SITES; i++ {       *)
  (*     site := new(TxnSite)                                *)
  (*     site.latch = new(sync.Mutex)                        *)
  (*     site.tidsActive = make([]uint64, 0, 8)              *)
  (*     txnMgr.sites[i] = site                              *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_ref_to); first auto.
  iIntros (iRef) "HiRef".
  wp_pures.
  iDestruct (is_slice_to_small with "HsitesL") as "HsitesS".
  set P := λ (n : u64), (∃ sitesL,
    "HsitesS" ∷ is_slice_small sites ptrT 1 (to_val <$> sitesL) ∗
    "%Hlength" ∷ (⌜Z.of_nat (length sitesL) = N.TXN_SITES⌝) ∗
    "#HsitesRP" ∷ ([∗ list] sid ↦ site ∈ (take (int.nat n) sitesL), is_txnsite site sid γ) ∗
    "Hsites" ∷ (txnmgr ↦[TxnMgr :: "sites"] (to_val sites)) ∗
    "HactiveAuths" ∷ ([∗ list] sid ∈ (drop (int.nat n) sids_all), site_active_tids_half_auth γ sid ∅) ∗
    "HminAuths" ∷ ([∗ list] sid ∈ (drop (int.nat n) sids_all), site_min_tid_half_auth γ sid 0))%I.
  wp_apply (wp_forUpto P _ _ (U64 0) (U64 N.TXN_SITES) with "[] [HsitesS $sites $HiRef HactiveAuths HminAuths]"); first done.
  { clear Φ latch.
    iIntros (i Φ) "!> (Hloop & HiRef & %Hbound) HΦ".
    iNamed "Hloop".
    wp_pures.
    wp_apply (wp_allocStruct); first auto 10.
    iIntros (site) "Hsite".
    iDestruct (struct_fields_split with "Hsite") as "Hsite".
    iNamed "Hsite".
    simpl.
    wp_pures.
    wp_apply (wp_new_free_lock).
    iIntros (latch) "Hfree".
    wp_storeField.
    (* wp_apply (wp_NewSlice (V:=u64)). *)
    wp_apply (wp_NewSliceWithCap (V:=u64)); first word.
    iIntros (active) "HactiveL".
    wp_storeField.
    wp_load.
    wp_loadField.
    replace (int.Z 64) with (Z.of_nat (length sitesL)) in Hbound.
    unfold N.TXN_SITES in *.
    wp_apply (wp_SliceSet with "[$HsitesS]").
    { iPureIntro.
      split; last auto.
      apply lookup_lt_is_Some.
      rewrite fmap_length.
      word.
    }
    iIntros "HsitesS".
    wp_pures.
    (* FIXME: Call `genTID` to get a lower bound. *)
    iAssert (ts_lb γ 1%nat)%I as "#Htslb".
    { admit. }
    iApply "HΦ".
    iFrame.
    
    rewrite (drop_S _ i); last first.
    { unfold sids_all, N.TXN_SITES.
      rewrite list_lookup_fmap.
      rewrite lookup_seqZ_lt; last word.
      simpl. f_equal. word.
    }
    iDestruct (big_sepL_cons with "HactiveAuths") as "[HactiveAuth HactiveAuths]".
    iDestruct (big_sepL_cons with "HminAuths") as "[HminAuth HminAuths]".
    iMod (readonly_alloc_1 with "latch") as "#Hlatch".
    iMod (alloc_lock mvccN _ latch (own_txnsite site i γ) with "[$Hfree] [-HsitesS HsitesRP HactiveAuths HminAuths]") as "#Hlock".
    { iNext.
      unfold own_txnsite.
      iExists (U64 0), (U64 0), (Slice.mk active 0 8), [], ∅.
      replace (int.nat (U64 0)) with 0%nat by word.
      iFrame "% # ∗".
      iPureIntro.
      split; first set_solver.
      split; first apply NoDup_nil_2.
      split; [by apply Forall_singleton | set_solver].
    }
    iModIntro.
    rewrite -list_fmap_insert.
    iExists _.
    iFrame.
    rewrite insert_length.
    iSplit; first done.
    replace (int.nat (word.add i 1)) with (S (int.nat i)); last word.
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
    replace (U64 _) with i by word.
    eauto with iFrame.
  }
  { iExists (replicate 64 null).
    auto with iFrame.
  }
  iIntros "[Hloop HiRef]".
  iNamed "Hloop".
  wp_pures.

  (***********************************************************)
  (* txnMgr.p = machine.NewProph()                           *)
  (***********************************************************)
  wp_apply (wp_NewProphActions γ).
  iIntros (p acs) "Hproph".
  (* FIXME: Cannot use tactic [wp_storeField]. *)
  wp_apply (wp_storeField with "p").
  { (* Prove [val_ty] *)
    admit.
  }
  iIntros "p".
  wp_pures.
  iMod (inv_alloc mvccNSST _ (mvcc_inv_sst_def γ p) with "[Hvchains']") as "#Hinv".
  { (* Prove [mvcc_inv_sst_def]. *)
    admit.
  }
  
  (***********************************************************)
  (* txnMgr.idx = index.MkIndex()                            *)
  (* txnMgr.gc = gc.MkGC(txnMgr.idx)                         *)
  (***********************************************************)
  wp_apply (wp_MkIndex γ with "Hinvgc Hinv Hvchains").
  iIntros (idx) "#HidxRP".
  wp_storeField.
  wp_loadField.
  wp_apply (wp_MkGC _ γ).
  (* iIntros (gc) "HgcRP". *)
  iIntros (gc) "_".
  wp_storeField.

  (***********************************************************)
  (* return txnMgr                                           *)
  (***********************************************************)
  iApply "HΦ".
  rewrite /is_txnmgr.
  iMod (readonly_alloc_1 with "latch") as "#Hlatch".
  iMod (alloc_lock mvccN _ latch (own_txnmgr txnmgr) with "[$Hfree] [sidCur]") as "#Hlock".
  { eauto with iFrame. }
  iMod (readonly_alloc_1 with "idx") as "#Hidx".
  iMod (readonly_alloc_1 with "gc") as "#Hgc".
  iMod (readonly_alloc_1 with "p") as "#Hp".
  iMod (readonly_alloc_1 with "Hsites") as "#Hsites".
  iMod (readonly_alloc_1 with "HsitesS") as "#HsitesS".
  replace (int.nat (U64 N.TXN_SITES)) with (length sitesL); last first.
  { unfold N.TXN_SITES in *. word. }
  rewrite firstn_all.
  do 6 iExists _.
  (* by iFrame "# %". *)
Admitted.

End program.
