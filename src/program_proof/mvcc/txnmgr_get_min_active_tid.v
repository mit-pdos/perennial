From Perennial.program_proof.mvcc Require Import
     txn_prelude txnmgr_repr
     tid_proof.

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
  (* tidnew = GenTID(sid)                                    *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first done.
  iIntros (tidRef) "HtidRef".
  wp_pures.
  wp_apply wp_GenTID.
  (* Open the SST invariant to get [ts_auth]. *)
  iInv "Hinvsst" as "> HinvsstO" "HinvsstC".
  iDestruct (mvcc_inv_sst_ts_auth_acc with "HinvsstO") as (ts) "[Hts HinvtsC]".
  (* Open the GC invariant. *)
  iInv "Hinvgc" as "> HinvgcO" "HinvgcC".
  iDestruct (big_sepL_lookup_acc with "HinvgcO") as "[HinvsiteO HinvsiteC]".
  { by apply sids_all_lookup. }
  iNamed "HinvsiteO".
  (* Obtain [tidmax ≤ ts]. *)
  iDestruct (ts_auth_lb_le with "Hts Htslb") as %Hle.
  (* Agree on the active TIDs obtained from lock and global invariants. *)
  iDestruct (site_active_tids_agree with "HactiveA HactiveAuth") as %->.
  (* Update the minimal TID to the smallest among [{[ ts ]} ∪ tidsactiveM]. *)
  set tids := {[ ts ]} ∪ tidsactiveM.
  assert (∃ tidmin', set_Forall (λ tid, (tidmin' ≤ tid)%nat) tids ∧ tidmin' ∈ tids)
    as (tidmin' & Htidmin' & Helem).
  { destruct (minimal_exists_L Nat.le tids) as (tidx & Htidx & Hminimal); first set_solver.
    exists tidx.
    split; last done.
    rewrite minimal_anti_symm in Hminimal.
    intros tidy Htidy.
    destruct (decide (tidx ≤ tidy)%nat); first done.
    apply Hminimal in Htidy; lia.
  }
  iMod (site_min_tid_update tidmin' with "HminA") as "HminA".
  { rewrite elem_of_union in Helem.
    destruct Helem; last by auto.
    (* Case [tidmin' = ts]. *)
    rewrite elem_of_singleton in H.
    rewrite H.
    apply set_Forall_union_inv_1, set_Forall_singleton in Hmax.
    lia.
  }
  iDestruct (site_min_tid_witness with "HminA") as "#Hminlb".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  (* Give atomic precondition. *)
  iExists _. iFrame "Hts".
  iIntros "(%ts' & Hts & %Hlt)".
  iClear "Htslb".
  iDestruct (ts_witness with "Hts") as "#Htslb".
  iMod "Hclose" as "_".
  (* Close the GC invariant. *)
  iDestruct ("HinvsiteC" with "[HactiveA HminA]") as "HinvsiteO".
  { iExists _, _, ts.
    iDestruct (ts_lb_weaken (S ts) with "Htslb") as "#Htslb'"; first lia.
    iFrame "∗ Htslb'".
    iPureIntro.
    split.
    { eapply set_Forall_subseteq; last apply Htidmin'. set_solver. }
    { (* apply set_Forall_union_inv_1 in Hmax as Hminmax.
      rewrite set_Forall_singleton in Hminmax. *)
      apply set_Forall_union.
      { rewrite set_Forall_singleton.
        apply set_Forall_union_inv_1 in Htidmin'.
        by rewrite set_Forall_singleton in Htidmin'.
      }
      { apply set_Forall_union_inv_2 in Hmax.
        eapply set_Forall_impl; first apply Hmax.
        word.
      }
    }
  }
  iMod ("HinvgcC" with "HinvsiteO") as "_".
  iDestruct ("HinvtsC" with "[] Hts") as "HinvsstO".
  { iPureIntro. lia. }
  iMod ("HinvsstC" with "HinvsstO") as "_".
  iModIntro.
  iIntros (tidnew) "%Etidnew".
  wp_store.
  
  (***********************************************************)
  (* machine.Assume(tidnew < 18446744073709551615)           *)
  (***********************************************************)
  wp_load.
  wp_apply wp_Assume.
  iIntros (Hoverflow).
  apply bool_decide_eq_true_1 in Hoverflow.
  
  (***********************************************************)
  (* var tidmin uint64 = tidnew                              *)
  (***********************************************************)
  wp_load.
  wp_apply (wp_ref_to); first by auto.
  iIntros (tidminRef) "HtidminRef".
  wp_pures.

  (***********************************************************)
  (* for _, tid := range site.tidsActive {                   *)
  (*     if tid < tidmin {                                   *)
  (*         tidmin = tid                                    *)
  (*     }                                                   *)
  (* }                                                       *)
  (***********************************************************)
  set u64_to_nat := (λ x : u64, int.nat x).
  iDestruct (is_slice_small_acc with "HactiveL") as "[HactiveS HactiveC]".
  wp_loadField.
  set P := λ (i : u64), (∃ (tidloop : u64), let tids := tidnew :: (take (int.nat i) tidsactiveL) in
    "HtidminRef" ∷ tidminRef ↦[uint64T] #tidloop ∗
    "%Helem'" ∷ ⌜tidloop ∈ tids⌝ ∗
    "%Htidloop" ∷ (⌜Forall (λ tid, (int.nat tidloop ≤ tid)%nat) (u64_to_nat <$> tids)⌝))%I.
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
      { rewrite app_comm_cons fmap_app.
        rewrite Forall_app.
        split.
        { apply (Forall_impl _ _ _ Htidloop). word. }
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
      { rewrite app_comm_cons fmap_app.
        rewrite Forall_app.
        split.
        { apply (Forall_impl _ _ _ Htidloop). word. }
        apply Forall_singleton. subst u64_to_nat. word.
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
  subst P. simpl. iNamed "Hloop".
  wp_pures.
  
  (***********************************************************)
  (* site.latch.Unlock()                                     *)
  (***********************************************************)
  iDestruct ("HactiveC" with "HactiveS") as "HactiveL".
  wp_loadField.
  wp_apply (release_spec with "[-HΦ HtidminRef]").
  { eauto 10 with iFrame. }
  wp_pures.

  (***********************************************************)
  (* return tidmin                                           *)
  (***********************************************************)
  (* Deduce [tidmin' = tidloop]. *)
  rewrite -HtidsactiveSz firstn_all in Htidloop Helem'.
  replace tidmin' with (int.nat tidloop); last first.
  { subst tids ts tidsactiveM.
    clear -Helem Htidmin' Helem' Htidloop.
    rewrite -list_to_set_cons elem_of_list_to_set in Helem.
    rewrite -list_to_set_cons set_Forall_list_to_set in Htidmin'.
    replace (int.nat tidnew) with (u64_to_nat tidnew) in Helem, Htidmin'; last done.
    rewrite -fmap_cons in Helem Htidmin'.
    apply (elem_of_list_fmap_1 u64_to_nat) in Helem'.
    rewrite Forall_forall in Htidmin'.
    rewrite Forall_forall in Htidloop.
    apply Htidmin' in Helem'.
    apply Htidloop in Helem.
    subst u64_to_nat. word.
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
