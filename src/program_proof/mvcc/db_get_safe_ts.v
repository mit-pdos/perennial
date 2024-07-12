From Perennial.program_proof.mvcc Require Import
     txn_prelude db_repr
     txnsite_get_safe_ts.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem wp_DB__getSafeTS db γ :
  is_db db γ -∗
  {{{ True }}}
    DB__getSafeTS #db
  {{{ (tid : u64), RET #tid; min_tid_lb γ (uint.nat tid) }}}.
Proof.
  iIntros "#Hdb" (Φ) "!> _ HΦ".
  wp_call.

  (*@ func (db *DB) getSafeTS() uint64 {                                      @*)
  (*@     var min uint64 = config.TID_SENTINEL                                @*)
  (*@                                                                         @*)
  wp_apply (wp_ref_to); first auto.
  iIntros (minRef) "HminRef".
  wp_pures.

  (*@     for sid := uint64(0); sid < config.N_TXN_SITES; sid++ {             @*)
  (*@         site := db.sites[sid]                                           @*)
  (*@         tid := site.GetSafeTS()                                         @*)
  (*@         if tid < min {                                                  @*)
  (*@             min = tid                                                   @*)
  (*@         }                                                               @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_apply (wp_ref_to); first auto.
  iIntros (sidRef) "HsidRef".
  wp_pures.
  set P := λ (i : u64), (∃ (tidmin : u64),
    "HminRef" ∷ minRef ↦[uint64T] #tidmin ∗
    "Htidlbs" ∷ [∗ list] sid ∈ (take (uint.nat i) sids_all), site_min_tid_lb γ sid (uint.nat tidmin))%I.
  wp_apply (wp_forUpto P _ _ (W64 0) (W64 N_TXN_SITES) sidRef with "[] [HminRef HsidRef]"); first done.
  { clear Φ.
    iIntros (i Φ) "!> (Hloop & HsidRef & %Hbound) HΦ".
    iNamed "Hloop".
    wp_pures.
    wp_load.

    iNamed "Hdb".
    list_elem sitesL (uint.nat i) as site.
    wp_loadField.
    iMod (readonly_load with "HsitesS") as (q) "HsitesS'".
    wp_apply (wp_SliceGet with "[$HsitesS']").
    { iPureIntro.
      rewrite list_lookup_fmap.
      by rewrite Hsite_lookup.
    }
    iIntros "[HsitesS' _]".
    wp_pures.
    iDestruct (big_sepL_lookup with "HsitesRP") as "HsiteRP"; first done.

    wp_apply (wp_TxnSite__GetSafeTS with "HsiteRP").
    iIntros (tid) "Htidlb".
    wp_pures.
    wp_load.
    wp_pures.

    replace (W64 (Z.of_nat _)) with i by word.
    wp_if_destruct.
    - (* Find new min. *)
      wp_store.
      iApply "HΦ".
      iModIntro.
      iFrame.
      replace (uint.nat (word.add _ _)) with (S (uint.nat i)); last by word.
      rewrite (take_S_r _ _ i); last by apply sids_all_lookup.
      iApply big_sepL_app.
      iSplitL "Htidlbs".
      { iApply (big_sepL_impl with "Htidlbs").
        iModIntro.
        iIntros (iN sid) "Hlookup Htidlb".
        (* Weaken all previous lower bounds. *)
        iApply (site_min_tid_lb_weaken with "Htidlb").
        word.
      }
      { simpl. iFrame. }
    - (* Same min. *)
      iApply "HΦ".
      iModIntro.
      iFrame.
      replace (uint.nat (word.add _ _)) with (S (uint.nat i)); last by word.
      rewrite (take_S_r _ _ i); last by apply sids_all_lookup.
      iApply big_sepL_app.
      iSplitL "Htidlbs"; first done.
      simpl.
      iSplit; last done.
      (* Weaken the current lower bound. *)
      iApply (site_min_tid_lb_weaken with "Htidlb").
      word.
  }
  { iFrame.
    replace (uint.nat 0) with 0%nat; last word.
    rewrite take_0.
    auto.
  }
  iIntros "[Hloop HsidRef]".
  iNamed "Hloop".
  wp_pures.

  (*@     return min                                                          @*)
  (*@ }                                                                       @*)
  wp_load.
  by iApply "HΦ".
Qed.

End program.
