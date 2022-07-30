From Perennial.program_proof.mvcc Require Import txn_common tid_proof.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (txnMgr *TxnMgr) getMinActiveTIDSite(sid uint64) uint64  *)
(*****************************************************************)
Theorem wp_txnMgr__getMinActiveTIDSite txnmgr (sid : u64) γ :
  is_txnmgr txnmgr γ -∗
  {{{ ⌜int.Z sid < int.Z N_TXN_SITES⌝ }}}
    TxnMgr__getMinActiveTIDSite #txnmgr #sid
  {{{ (tid : u64), RET #tid; site_min_tid_lb γ sid (int.nat tid) }}}.
Proof.
  iIntros "#Htxnmgr" (Φ) "!> %Hbound HΦ".
  iNamed "Htxnmgr".
  iMod (readonly_load with "HsitesS") as (q) "HsitesS'".
  wp_call.

  (***********************************************************)
  (* site := txnMgr.sites[sid]                               *)
  (***********************************************************)
  wp_loadField.
  list_elem sitesL (int.nat sid) as site.
  { revert HsitesLen. unfold N_TXN_SITES in *. word. }
  wp_apply (wp_SliceGet with "[$HsitesS']").
  { iPureIntro.
    rewrite list_lookup_fmap.
    by rewrite Hsite_lookup.
  }
  iIntros "[HsitesS' _]".
  wp_pures.
  
  (***********************************************************)
  (* site.latch.Lock()                                       *)
  (***********************************************************)
  iDestruct (big_sepL_lookup with "HsitesRP") as "HsiteRP"; first done.
  iClear (latch) "Hlatch Hlock".
  iNamed "HsiteRP".
  wp_loadField.
  wp_apply (acquire_spec with "[$Hlock]").
  iIntros "[Hlocked HsiteOwn]".
  replace (U64 (Z.of_nat _)) with sid by word. 
  iNamed "HsiteOwn".
  iDestruct (typed_slice.is_slice_sz with "HactiveL") as "%HtidsactiveSz".
  wp_pures.
  
  (***********************************************************)
  (* var tidnew uint64                                       *)
  (* tidnew = genTID(sid)                                    *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first done.
  iIntros (tidnewRef) "HtidnewRef".
  wp_pures.
  wp_apply (wp_genTID).
  iInv "Hinvsst" as "> HinvO" "HinvC".
  iNamed "HinvO".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iExists ts.
  (* Deduce [tslast < ts] with [Hts] and [Htslb]. *)
  iDestruct (ts_auth_lb_le with "Hts Htslb") as "%HltN".
  iFrame "Hts".
  iIntros "[%n [Hts %Hgz]]".
  (* Before we close the invariant, obtain a witness of a LB of timestamp. *)
  iAssert (ts_lb γ (S ts))%I as "#Htslb'".
  { iDestruct (ts_witness with "Hts") as "#H".
    iApply (ts_lb_weaken with "H"). lia.
  }
  iMod "Hclose" as "_".
  iMod ("HinvC" with "[Hproph Hts Hm Hkeys Hcmt Hnca Hfa Hfci Hfcc]") as "_".
  { iNext.
    iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
    { iIntros (k) "%Helem Hkeys".
      iApply (per_key_inv_weaken_ts (ts + n)%nat with "Hkeys"). lia.
    }
    iDestruct (nca_inv_weaken_ts (ts + n)%nat with "Hnca") as "Hnca"; first lia.
    iDestruct (fa_inv_weaken_ts (ts + n)%nat with "Hfa") as "Hfa"; first lia.
    iDestruct (fci_inv_weaken_ts (ts + n)%nat with "Hfci") as "Hfci"; first lia.
    iDestruct (fcc_inv_weaken_ts (ts + n)%nat with "Hfcc") as "Hfcc"; first lia.
    iDestruct (cmt_inv_weaken_ts (ts + n)%nat with "Hcmt") as "Hcmt"; first lia.
    eauto 20 with iFrame.
  }
  iIntros "!>" (tidnew) "%Etidnew".
  assert (Hlt : int.Z tidlast < int.Z tidnew) by lia.
  wp_store.
  
  (***********************************************************)
  (* machine.Assume(tidnew < 18446744073709551615)           *)
  (***********************************************************)
  wp_load.
  wp_apply wp_Assume.
  iIntros "%Htidmax".
  apply bool_decide_eq_true_1 in Htidmax.
  
  (***********************************************************)
  (* site.tidLast = tidnew                                   *)
  (* var tidmin uint64 = tidnew                              *)
  (***********************************************************)
  wp_load.
  wp_storeField.
  wp_load.
  wp_apply (wp_ref_to); first auto.
  iIntros (tidminRef) "HtidminRef".
  wp_pures.

  (***********************************************************)
  (* for _, tid := range site.tidsActive {                   *)
  (*     if tid < tidmin {                                   *)
  (*         tidmin = tid                                    *)
  (*     }                                                   *)
  (* }                                                       *)
  (***********************************************************)
  iDestruct (is_slice_small_acc with "HactiveL") as "[HactiveS HactiveC]".
  wp_loadField.
  set P := λ (i : u64), (∃ (tidmin : u64), let tids := tidnew :: (take (int.nat i) tidsactiveL) in
    "HtidminRef" ∷ tidminRef ↦[uint64T] #tidmin ∗
    "%Helem" ∷ ⌜tidmin ∈ tids⌝ ∗
    "%HtidminLe" ∷ (⌜Forall (λ tid, int.Z tidmin ≤ int.Z tid) tids⌝))%I.
  wp_apply (typed_slice.wp_forSlice P _ _ _ _ _ tidsactiveL with "[] [HtidminRef $HactiveS]").
  { clear Φ.
    iIntros (i tidx Φ) "!> (Hloop & %Hbound' & %Hlookup) HΦ".
    iNamed "Hloop".
    wp_load.
    wp_if_destruct.
    - wp_store.
      iApply "HΦ".
      iModIntro.
      iExists _.
      iFrame.
      do 2 replace (int.nat (word.add i 1)) with (S (int.nat i)) by word.
      rewrite (take_S_r _ _ tidx); last done.
      iSplit; iPureIntro.
      { set_solver. }
      { rewrite app_comm_cons.
        rewrite Forall_app.
        split.
        { apply (Forall_impl _ _ _ HtidminLe). word. }
        apply Forall_singleton. done.
      }
    - iApply "HΦ".
      iModIntro.
      iExists _.
      iFrame.
      do 2 replace (int.nat (word.add i 1)) with (S (int.nat i)) by word.
      rewrite (take_S_r _ _ tidx); last done.
      iSplit; iPureIntro.
      { set_solver. }
      { rewrite app_comm_cons.
        rewrite Forall_app.
        split.
        { apply (Forall_impl _ _ _ HtidminLe). word. }
        apply Forall_singleton. word.
      }
  }
  { iExists _.
    iFrame.
    iPureIntro.
    rewrite take_0.
    rewrite Forall_forall.
    split; set_solver.
  }
  iIntros "[Hloop HactiveS]".
  iNamed "Hloop".
  rename tidmin0 into tidmin'.
  rewrite -HtidsactiveSz in Helem HtidminLe.
  rewrite firstn_all in Helem HtidminLe.

  (* Prove that we can safely update the local lower bound. *)
  assert (Hle : int.Z tidmin ≤ int.Z tidmin').
  { apply elem_of_cons in Helem.
    destruct Helem.
    - rewrite H.
      apply Forall_inv in HtidOrder. word.
    - apply Forall_inv_tail in HtidOrder.
      rewrite Forall_forall in HtidOrder.
      apply HtidOrder. done.
  }
  
  (* Open the global invariant to update [tidmin]. *)
  wp_apply (fupd_wp).
  iInv "Hinvgc" as ">HinvgcO" "HinvgcC".
  iDestruct (big_sepL_lookup_acc with "HinvgcO") as "[HinvgcO HinvgcOAcc]".
  { by apply sids_all_lookup. }
  iDestruct "HinvgcO" as (tidsM tidmin'') "(HactiveAuth' & HminAuth' & Hmin)".
  (* Agree on the set of active tids. *)
  iDestruct (site_active_tids_agree with "HactiveAuth' HactiveAuth") as %->.
  (* Update the minimal tid. *)
  iDestruct (site_min_tid_agree with "HminAuth' HminAuth") as %->.
  clear tidmin''.
  iMod (site_min_tid_update (int.nat tidmin') with "HminAuth' HminAuth") as "[HminAuth' HminAuth]"; first word.
  
  (* Close the global invariant. *)
  iDestruct ("HinvgcOAcc" with "[HactiveAuth' HminAuth' Hmin]") as "HinvgcO".
  { do 2 iExists _.
    iFrame "HactiveAuth' HminAuth'".
    iPureIntro.
    unfold set_Forall.
    apply Forall_inv_tail in HtidminLe.
    rewrite Forall_forall in HtidminLe.
    rewrite -HactiveLM.
    setoid_rewrite elem_of_list_to_set.
    intros ? Hx. specialize (HtidminLe _ Hx). word.
  }
  iMod ("HinvgcC" with "[HinvgcO]") as "_"; first done.
  iModIntro.

  (* Obtaining [site_min_tid_lb] for the postcondition. *)
  iDestruct (site_min_tid_witness with "HminAuth") as "#HminLb".
  
  (***********************************************************)
  (* site.latch.Unlock()                                     *)
  (* return tidmin                                           *)
  (***********************************************************)
  iDestruct ("HactiveC" with "HactiveS") as "HactiveL".
  wp_loadField.
  wp_apply (release_spec with "[-HΦ HtidminRef]").
  { iFrame "Hlock Hlocked".
    iNext.
    iExists tidnew.
    rewrite Etidnew.
    do 4 iExists _.
    iClear "Htslb".
    iFrame "% # ∗".
    iSplit; iPureIntro.
    { apply Forall_and.
      split; first done.
      apply Forall_cons.
      split; first word.
      apply Forall_inv_tail, Forall_and in HtidOrder.
      destruct HtidOrder as [_ HtidOrder].
      apply (Forall_impl _ _ _ HtidOrder).
      word.
    }
    split; last done.
    { intros tidx Hlt'. apply HtidFree. word. }
  }
  wp_load.
  by iApply "HΦ".
Qed.

(*****************************************************************)
(* func (txnMgr *TxnMgr) getMinActiveTID() uint64                *)
(*****************************************************************)
Theorem wp_txnMgr__getMinActiveTID txnmgr γ :
  is_txnmgr txnmgr γ -∗
  {{{ True }}}
    TxnMgr__getMinActiveTID #txnmgr
  {{{ (tid : u64), RET #tid; min_tid_lb γ (int.nat tid) }}}.
Proof.
  iIntros "#Htxnmgr" (Φ) "!> _ HΦ".
  wp_call.
  
  (***********************************************************)
  (* var min uint64 = config.TID_SENTINEL                    *)
  (***********************************************************)
  wp_apply (wp_ref_to); first auto.
  iIntros (minRef) "HminRef".
  wp_pures.
    
  (***********************************************************)
  (* for sid := uint64(0); sid < config.N_TXN_SITES; sid++ { *)
  (*     tid := txnMgr.getMinActiveTIDSite(sid)              *)
  (*     if tid < min {                                      *)
  (*         min = tid                                       *)
  (*     }                                                   *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_ref_to); first auto.
  iIntros (sidRef) "HsidRef".
  wp_pures.
  set P := λ (i : u64), (∃ (tidmin : u64),
    "HminRef" ∷ minRef ↦[uint64T] #tidmin ∗
    "Htidlbs" ∷ [∗ list] sid ∈ (take (int.nat i) sids_all), site_min_tid_lb γ sid (int.nat tidmin))%I.
  wp_apply (wp_forUpto P _ _ (U64 0) (U64 N_TXN_SITES) sidRef with "[] [HminRef HsidRef]"); first done.
  { clear Φ.
    iIntros (i Φ) "!> (Hloop & HsidRef & %Hbound) HΦ".
    iNamed "Hloop".
    wp_pures.
    wp_load.
    wp_apply (wp_txnMgr__getMinActiveTIDSite with "Htxnmgr"); first done.
    iIntros (tid) "Htidlb".
    wp_pures.
    wp_load.
    wp_pures.

    wp_if_destruct.
    - (* Find new min. *)
      wp_store.
      iApply "HΦ".
      iModIntro.
      iFrame.
      iExists _.
      iFrame.
      replace (int.nat (word.add _ _)) with (S (int.nat i)); last by word.
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
      { simpl. auto. }
    - (* Same min. *)
      iApply "HΦ".
      iModIntro.
      iFrame.
      iExists _.
      iFrame.
      replace (int.nat (word.add _ _)) with (S (int.nat i)); last by word.
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
    iExists _.
    iFrame.
    replace (int.nat 0) with 0%nat; last word.
    rewrite take_0.
    auto.
  }
  iIntros "[Hloop HsidRef]".
  iNamed "Hloop".
  wp_pures.
  
  (***********************************************************)
  (* return min                                              *)
  (***********************************************************)
  wp_load.
  by iApply "HΦ".
Qed.

End program.
