From Perennial.program_proof.mvcc Require Import txn_common.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func swapWithEnd(xs []uint64, i uint64)                       *)
(*****************************************************************)
Local Theorem wp_swapWithEnd (xsS : Slice.t) (xs : list u64) (i : u64) (x : u64) :
  {{{ typed_slice.is_slice xsS uint64T 1 xs ∧ (⌜xs !! (int.nat i) = Some x⌝) }}}
    swapWithEnd (to_val xsS) #i
  {{{ (xs' : list u64), RET #(); typed_slice.is_slice xsS uint64T 1 (xs' ++ [x]) ∧
                                 (⌜xs' ≡ₚ delete (int.nat i) xs⌝)
  }}}.
Proof.
  iIntros (Φ) "[HtidsS %Hlookup] HΦ".
  wp_call.
  iDestruct (is_slice_sz with "HtidsS") as "%HtidsSz".
  iDestruct (typed_slice.is_slice_small_acc with "HtidsS") as "[HtidsS HtidsC]".
  rewrite fmap_length in HtidsSz.
  assert (Hgz : int.Z xsS.(Slice.sz) > 0).
  { apply lookup_lt_Some in Hlookup. word. }

  (***********************************************************)
  (* tmp := xs[len(xs) - 1]                                  *)
  (***********************************************************)
  wp_apply wp_slice_len.
  wp_pures.
  set idxlast := word.sub _ _.
  assert (Hidxlast : int.Z idxlast = (int.Z xsS.(Slice.sz)) - 1).
  { subst idxlast. word. }
  assert (HlookupLast : (int.nat idxlast < length xs)%nat) by word.
  apply list_lookup_lt in HlookupLast as [xlast HlookupLast].
  (* wp_apply (typed_slice.wp_SliceGet (V:=u64) with "[HtidsS]"). *)
  wp_apply (typed_slice.wp_SliceGet with "[$HtidsS]").
  { iFrame.
    iPureIntro.
    by rewrite HlookupLast.
  }
  iIntros "HtidsS".
    
  (***********************************************************)
  (* xs[len(xs) - 1] = xs[i]                                 *)
  (***********************************************************)
  wp_pures.
  wp_apply (typed_slice.wp_SliceGet with "[$HtidsS]").
  { iFrame.
    iPureIntro.
    by rewrite Hlookup.
  }
  iIntros "HtidsS".
  wp_apply wp_slice_len.
  wp_pures.
  wp_apply (typed_slice.wp_SliceSet with "[$HtidsS]").
  { iFrame.
    iPureIntro.
    by rewrite HlookupLast.
  }
  iIntros "HtidsS".
  wp_pures.

  (***********************************************************)
  (* xs[i] = tmp                                             *)
  (***********************************************************)
  wp_apply (typed_slice.wp_SliceSet with "[$HtidsS]").
  { iFrame.
    iPureIntro.
    apply lookup_lt_is_Some_2.
    rewrite insert_length.
    by eapply lookup_lt_Some.
  }
  iIntros "HtidsS".
  iDestruct ("HtidsC" with "HtidsS") as "HtidsS".
  wp_pures.

  destruct (decide (pred (length xs) ≤ int.nat i)%nat).
  - (* Case: [i = idxlast]. *)
    iApply "HΦ".
    iModIntro.
    subst idxlast.
    replace (int.nat (word.sub _ _)) with (pred (length xs)) in *; last word.
    apply lookup_lt_Some in Hlookup as Hlt.
    { assert (Ei : (int.nat i) = pred (length xs)) by lia.
      rewrite Ei.
      rewrite list_insert_insert.
      rewrite list_insert_at_end; last set_solver.
      replace x with xlast; last first.
      { rewrite Ei in Hlookup. set_solver. }
      iFrame.
      iPureIntro.
      rewrite delete_take_drop.
      replace (drop _ _) with ([] : list u64); last first.
      { replace (S _) with (length xs); last lia. by rewrite drop_all. }
      rewrite app_nil_r.
      by rewrite removelast_firstn_len.
    }
  - (* Case: [i ≠ idxlast]. *)
    iApply "HΦ".
    iModIntro.
    apply Nat.nle_gt in n.
    replace (int.nat (word.sub _ _)) with (pred (length xs)); last word.
    rewrite list_insert_at_end; last set_solver.
    rewrite insert_app_l; last first.
    { rewrite removelast_firstn_len. rewrite take_length_le; word. }
    iFrame.
    iPureIntro.
    apply list_swap_with_end with x; [done | | done].
    rewrite -HlookupLast.
    replace (int.nat idxlast) with (pred (length xs)); last word.
    apply last_lookup.
Qed.

(*****************************************************************)
(* func findTID(tid uint64, tids []uint64) uint64                *)
(*****************************************************************)
Local Theorem wp_findTID (tid : u64) (tidsS : Slice.t) (tids : list u64) :
  {{{ typed_slice.is_slice tidsS uint64T 1 tids ∗ ⌜tid ∈ tids⌝ }}}
    findTID #tid (to_val tidsS)
  {{{ (idx : u64), RET #idx; typed_slice.is_slice tidsS uint64T 1 tids ∧
                             (⌜tids !! (int.nat idx) = Some tid⌝)
  }}}.
Proof.
  iIntros (Φ) "[HtidsS %Helem] HΦ".
  wp_call.

  (***********************************************************)
  (* var idx uint64 = 0                                      *)
  (***********************************************************)
  wp_apply (wp_ref_to); first auto.
  iIntros (idxRef) "HidxRef".
  wp_pures.
  
  (***********************************************************)
  (* for {                                                   *)
  (*     tidx := tids[idx]                                   *)
  (*     if tid == tidx {                                    *)
  (*         break                                           *)
  (*     }                                                   *)
  (*     idx++                                               *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool), (∃ (idx : u64),
    "HidxRef" ∷ idxRef ↦[uint64T] #idx ∗
    "HtidsS" ∷  typed_slice.is_slice tidsS uint64T 1 tids ∗
    "%Hne" ∷ (⌜Forall (λ tidx, tidx ≠ tid) (take (int.nat idx) tids)⌝) ∗
    "%Hbound" ∷ ⌜(int.Z idx < Z.of_nat (length tids))⌝ ∗
    "%Hexit" ∷ (⌜if b then True else tids !! (int.nat idx) = Some tid⌝))%I.
  wp_apply (wp_forBreak P with "[] [HidxRef HtidsS]").
  { clear Φ.
    iIntros (Φ) "!> Hloop HΦ".
    iNamed "Hloop".
    wp_pures.
    wp_load.
    assert (Hlookup : (int.nat idx < length tids)%nat) by word.
    apply list_lookup_lt in Hlookup as [tidx Hlookup].
    iDestruct (is_slice_small_acc with "HtidsS") as "[HtidsS HtidsC]".
    wp_apply (wp_SliceGet with "[HtidsS]").
    { iFrame.
      iPureIntro.
      rewrite list_lookup_fmap.
      by rewrite Hlookup.
    }
    iIntros "[HtidsS %HtidsVT]".
    iDestruct ("HtidsC" with "HtidsS") as "HtidsS".
    wp_pures.
    wp_if_destruct.
    { iApply "HΦ". unfold P. eauto with iFrame. }
    wp_load.
    wp_store.
    iApply "HΦ".
    iModIntro.
    iExists _.
    iDestruct (is_slice_sz with "HtidsS") as "%HtidsSz".
    rewrite fmap_length in HtidsSz.
    iFrame "% ∗".
    iPureIntro.
    split.
    { replace (int.nat _) with (S (int.nat idx)); last word.
      rewrite (take_S_r _ _ tidx); last done.
      apply Forall_app_2; first done.
      apply Forall_singleton.
      apply u64_val_ne in Heqb.
      unfold not. intros H. rewrite H in Heqb. word.
    }
    { destruct (decide (int.Z idx < Z.of_nat (length tids) - 1)); first word.
      apply Znot_lt_ge in n.
      assert (Hexists: Exists (λ tidx : u64, tidx = tid) tids).
      { rewrite Exists_exists. by exists tid. }
      destruct (Exists_not_Forall (λ tidx : u64, tidx ≠ tid) tids).
      { apply (Exists_impl _ _ _ Hexists). auto. }
      replace tids with (take (S (int.nat idx)) tids); last first.
      { rewrite take_ge; [done | word]. }
      rewrite (take_S_r _ _ tidx); last done.
      apply Forall_app_2; first done.
      apply Forall_singleton.
      apply u64_val_ne in Heqb.
      unfold not. intros H. rewrite H in Heqb. word.
    }
  }
  { iExists _.
    iFrame.
    iPureIntro.
    split.
    { change (int.nat 0) with 0%nat. by rewrite take_0. }
    split; last done.
    { apply elem_of_list_lookup in Helem as [i Hlookup].
      apply lookup_lt_Some in Hlookup. word.
    }
  }
  iIntros "Hloop".
  iNamed "Hloop".
  wp_pures.
  
  (***********************************************************)
  (* return idx                                              *)
  (***********************************************************)
  wp_load.
  iApply "HΦ".
  by iFrame.
Qed.

(*****************************************************************)
(* func (txnMgr *TxnMgr) deactivate(sid uint64, tid uint64)      *)
(*****************************************************************)
Local Theorem wp_txnMgr__deactivate txnmgr (sid tid : u64) γ :
  is_txnmgr txnmgr γ -∗
  {{{ active_tid γ tid sid }}}
    TxnMgr__deactivate #txnmgr #sid #tid
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htxnmgr" (Φ) "!> Hactive HΦ".
  iNamed "Htxnmgr".
  wp_call.

  (***********************************************************)
  (* site := txnMgr.sites[sid]                               *)
  (***********************************************************)
  wp_loadField.
  iMod (readonly_load with "HsitesS") as (q) "HsitesS'".
  iDestruct "Hactive" as "[[HactiveFrag %Hbound] _]".
  list_elem sitesL (int.nat sid) as site.
  wp_apply (wp_SliceGet with "[$HsitesS']").
  { iPureIntro.
    rewrite list_lookup_fmap.
    by rewrite Hsite_lookup.
  }
  iIntros "[HsitesS' %HsiteVT]".
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
  iDestruct (is_slice_sz with "HactiveL") as "%HactiveSz".
  rewrite fmap_length in HactiveSz.
  wp_pures.
  
  (*****************************************************************)
  (* idx := findTID(tid, site.tidsActive)                          *)
  (*****************************************************************)
  wp_loadField.
  iDestruct (site_active_tids_elem_of with "HactiveAuth HactiveFrag") as "%Hin".
  rewrite -HactiveLM elem_of_list_to_set in Hin.
  wp_apply (wp_findTID tid _ tidsactiveL with "[$HactiveL]"); first auto.
  iIntros (pos) "[HactiveL %Hlookup]".
  wp_pures.
  
  (*****************************************************************)
  (* swapWithEnd(site.tidsActive, idx)                             *)
  (*****************************************************************)
  wp_loadField.
  wp_apply (wp_swapWithEnd with "[HactiveL]"); first by iFrame.
  iIntros (tids) "[HactiveL %Hperm]".
  wp_pures.
  
  (*****************************************************************)
  (* site.tidsActive = site.tidsActive[:len(site.tidsActive) - 1]  *)
  (*****************************************************************)
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_loadField.
  iDestruct (is_slice_wf with "HactiveL") as "%HtidsactiveCap".
  wp_apply (wp_SliceTake).
  { apply lookup_lt_Some in Hlookup. word. }
  wp_storeField.
  wp_loadField.

  (* Open the global invariant to update the local active TIDs. *)
  iApply fupd_wp.
  iInv "Hinvgc" as ">HinvgcO" "HinvgcC".
  iDestruct (big_sepL_lookup_acc with "HinvgcO") as "[HinvgcO HinvgcOAcc]".
  { by apply sids_all_lookup. }
  iDestruct "HinvgcO" as (tidsM tidmin') "(HactiveAuth' & HminAuth' & %Hmin)".
  (* Update the set of active tids. *)
  iDestruct (site_active_tids_agree with "HactiveAuth' HactiveAuth") as %->.
  iMod (site_active_tids_delete tid with "HactiveFrag HactiveAuth' HactiveAuth") as "[HactiveAuth' HactiveAuth]".
  (* Close the global invariant. *)
  iDestruct ("HinvgcOAcc" with "[HactiveAuth' HminAuth']") as "HinvgcO".
  { do 2 iExists _.
    iFrame "HactiveAuth' HminAuth'".
    iPureIntro.
    rewrite dom_delete_L.
    set_solver.
  }
  iMod ("HinvgcC" with "[HinvgcO]") as "_"; first done.
  iModIntro.
  
  (*****************************************************************)
  (* site.latch.Unlock()                                           *)
  (*****************************************************************)
  wp_apply (release_spec with "[-HΦ]").
  { iFrame "Hlock Hlocked".
    iNext.
    set idxlast := (word.sub _ _).
    iExists _, _, _, tids, _.
    iFrame "Hactive".
    iFrame "∗ #".
    assert (Hidxlast : int.nat idxlast = length tids).
    { subst idxlast.
      rewrite (Permutation_length Hperm).
      rewrite length_delete; last done.
      assert (H : (int.nat tidsactive.(Slice.sz) > 0)%nat).
      { rewrite -HactiveSz. apply lookup_lt_Some in Hlookup. lia. }
      rewrite HactiveSz. word.
    }
    iSplitL "HactiveL".
    { (* Prove [HactiveL]. *)
      unfold typed_slice.is_slice.
      unfold list.untype.
      iDestruct (is_slice_take_cap _ _ _ idxlast with "HactiveL") as "H".
      { rewrite fmap_length. rewrite last_length. word. }
      unfold named.
      iExactEq "H".
      rewrite -fmap_take.
      do 2 f_equal.
      replace (int.nat idxlast) with (length tids).
      apply take_app.
    }
    iSplit.
    { (* Prove [HactiveLM]. *)
      iPureIntro.
      rewrite (list_to_set_perm_L _ (delete (int.nat pos) tidsactiveL)); last done.
      rewrite dom_delete_L.
      rewrite -HactiveLM.
      rewrite delete_take_drop.
      apply take_drop_middle in Hlookup.
      rewrite <- Hlookup at 3.
      do 2 rewrite list_to_set_app_L.
      rewrite list_to_set_cons.
      set s1 := (list_to_set (take _ _)).
      set s2 := (list_to_set (drop _ _)).
      do 2 rewrite difference_union_distr_l_L.
      rewrite -Hlookup in HactiveND.
      apply NoDup_app in HactiveND as [_ [Hnotins1 Hnotins2]].
      apply NoDup_cons in Hnotins2 as [Hnotins2 _].
      replace (s1 ∖ {[tid]}) with s1 by set_solver.
      replace (s2 ∖ {[tid]}) with s2 by set_solver.
      set_solver.
    }
    iPureIntro.
    split.
    { (* Prove [HactiveND]. *)
      apply (NoDup_Permutation_proper _ _ Hperm).
      rewrite delete_take_drop.
      apply take_drop_middle in Hlookup.
      rewrite -Hlookup in HactiveND.
      apply NoDup_app in HactiveND as [HND1 [Hnotin1 HND2]].
      apply NoDup_cons in HND2 as [_ HND2].
      apply NoDup_app.
      split; first done.
      split; last done.
      set_solver.
    }
    split.
    { (* Prove [HtidOrder] *)
      apply Forall_cons_2; first by apply Forall_inv in HtidOrder.
      apply Forall_inv_tail in HtidOrder.
      apply (Forall_Permutation _ _ _ Hperm).
      by apply Forall_delete.
    }
    split; last done.
    { (* Prove [HtidFree]. *)
      simpl.
      intros tidx Htidx.
      apply not_elem_of_weaken with (dom tidsactiveM); last set_solver.
      auto.
    }
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End program.
