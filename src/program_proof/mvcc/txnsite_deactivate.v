From Perennial.program_proof.mvcc Require Import txnsite_prelude.
From Perennial.program_proof.mvcc Require Import txnsite_repr.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func swapWithEnd(xs []uint64, i uint64)                       *)
(*****************************************************************)
#[local]
Theorem wp_swapWithEnd (xsS : Slice.t) (xs : list u64) (i : u64) (x : u64) :
  {{{ typed_slice.own_slice xsS uint64T (DfracOwn 1) xs ∧ (⌜xs !! (uint.nat i) = Some x⌝) }}}
    swapWithEnd (to_val xsS) #i
  {{{ (xs' : list u64), RET #(); typed_slice.own_slice xsS uint64T (DfracOwn 1) (xs' ++ [x]) ∧
                                 (⌜xs' ≡ₚ delete (uint.nat i) xs⌝)
  }}}.
Proof.
  iIntros (Φ) "[HtidsS %Hlookup] HΦ".
  wp_call.
  iDestruct (own_slice_sz with "HtidsS") as "%HtidsSz".
  iDestruct (typed_slice.own_slice_small_acc with "HtidsS") as "[HtidsS HtidsC]".
  rewrite fmap_length in HtidsSz.
  assert (Hgz : uint.Z xsS.(Slice.sz) > 0).
  { apply lookup_lt_Some in Hlookup. word. }

  (***********************************************************)
  (* tmp := xs[len(xs) - 1]                                  *)
  (***********************************************************)
  wp_apply wp_slice_len.
  wp_pures.
  set idxlast := word.sub _ _.
  assert (Hidxlast : uint.Z idxlast = (uint.Z xsS.(Slice.sz)) - 1).
  { subst idxlast. word. }
  assert (HlookupLast : (uint.nat idxlast < length xs)%nat) by word.
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

  destruct (decide (pred (length xs) ≤ uint.nat i)%nat).
  - (* Case: [i = idxlast]. *)
    iApply "HΦ".
    iModIntro.
    subst idxlast.
    replace (uint.nat (word.sub _ _)) with (pred (length xs)) in *; last word.
    apply lookup_lt_Some in Hlookup as Hlt.
    { assert (Ei : (uint.nat i) = pred (length xs)) by lia.
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
    replace (uint.nat (word.sub _ _)) with (pred (length xs)); last word.
    rewrite list_insert_at_end; last set_solver.
    rewrite insert_app_l; last first.
    { rewrite removelast_firstn_len. rewrite take_length_le; word. }
    iFrame.
    iPureIntro.
    apply list_swap_with_end with x; [done | | done].
    rewrite -HlookupLast.
    replace (uint.nat idxlast) with (pred (length xs)); last word.
    apply last_lookup.
Qed.

(*****************************************************************)
(* func findTID(tid uint64, tids []uint64) uint64                *)
(*****************************************************************)
#[local]
Theorem wp_findTID (tid : u64) (tidsS : Slice.t) (tids : list u64) :
  {{{ typed_slice.own_slice tidsS uint64T (DfracOwn 1) tids ∗ ⌜tid ∈ tids⌝ }}}
    findTID #tid (to_val tidsS)
  {{{ (idx : u64), RET #idx; typed_slice.own_slice tidsS uint64T (DfracOwn 1) tids ∧
                             (⌜tids !! (uint.nat idx) = Some tid⌝)
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
  (* for tid != tids[idx] {                                  *)
  (*     idx++                                               *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool), (∃ (idx : u64),
    "HidxRef" ∷ idxRef ↦[uint64T] #idx ∗
    "HtidsS" ∷  typed_slice.own_slice tidsS uint64T (DfracOwn 1) tids ∗
    "%Hne" ∷ (⌜Forall (λ tidx, tidx ≠ tid) (take (uint.nat idx) tids)⌝) ∗
    "%Hbound" ∷ ⌜(uint.Z idx < Z.of_nat (length tids))⌝ ∗
    "%Hexit" ∷ (⌜if b then True else tids !! (uint.nat idx) = Some tid⌝))%I.
  wp_apply (wp_forBreak_cond P with "[] [HidxRef HtidsS]").
  { clear Φ.
    iIntros (Φ) "!> Hloop HΦ".
    iNamed "Hloop".
    wp_pures.
    wp_load.
    assert (Hlookup : (uint.nat idx < length tids)%nat) by word.
    apply list_lookup_lt in Hlookup as [tidx Hlookup].
    iDestruct (own_slice_small_acc with "HtidsS") as "[HtidsS HtidsC]".
    wp_apply (wp_SliceGet with "[HtidsS]").
    { iFrame.
      iPureIntro.
      rewrite list_lookup_fmap.
      by rewrite Hlookup.
    }
    iIntros "[HtidsS %HtidsVT]".
    iDestruct ("HtidsC" with "HtidsS") as "HtidsS".
    wp_pures.
    wp_if_destruct; last first.
    { iApply "HΦ". unfold P. eauto with iFrame. }
    wp_load.
    wp_store.
    iApply "HΦ".
    iModIntro.
    iExists _.
    iDestruct (own_slice_sz with "HtidsS") as "%HtidsSz".
    rewrite fmap_length in HtidsSz.
    iFrame "∗%".
    iPureIntro.
    split.
    { replace (uint.nat _) with (S (uint.nat idx)); last word.
      rewrite (take_S_r _ _ tidx); last done.
      apply Forall_app_2; first done.
      apply Forall_singleton.
      apply u64_val_ne in Heqb.
      unfold not. intros H. rewrite H in Heqb. word.
    }
    { destruct (decide (uint.Z idx < Z.of_nat (length tids) - 1)); first word.
      apply Znot_lt_ge in n.
      assert (Hexists: Exists (λ tidx : u64, tidx = tid) tids).
      { rewrite Exists_exists. by exists tid. }
      destruct (Exists_not_Forall (λ tidx : u64, tidx ≠ tid) tids).
      { apply (Exists_impl _ _ _ Hexists). auto. }
      replace tids with (take (S (uint.nat idx)) tids); last first.
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
    { change (uint.nat 0) with 0%nat. by rewrite take_0. }
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

#[local]
 Lemma u64_elem_of_fmap (x : u64) (l : list u64) :
  uint.nat x ∈ (λ (w : u64), uint.nat w) <$> l ->
  x ∈ l.
Proof.
  intros H.
  apply elem_of_list_fmap_2 in H as (y & Hxy & Helem).
  assert (Exy : x = y) by word.
  by rewrite Exy.
Qed.

Theorem wp_TxnSite__Deactivate site (sid tid : u64) γ :
  is_txnsite site sid γ -∗
  {{{ active_tid γ tid sid }}}
    TxnSite__Deactivate #site #tid
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Hsite" (Φ) "!> Hactive HΦ".
  iNamed "Hsite".
  wp_call.
  
  (*@ func (site *TxnSite) Deactivate(tid uint64) {                           @*)
  (*@     // Require @site.tids contains @tid.                                @*)
  (*@     site.latch.Lock()                                                   @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_apply (acquire_spec with "[$Hlock]").
  iIntros "[Hlocked HsiteOwn]".
  iNamed "HsiteOwn".
  iDestruct (own_slice_sz with "HactiveL") as "%HactiveSz".
  rewrite fmap_length in HactiveSz.
  wp_pures.

  (*@     // Remove @tid from the set of active transactions.                 @*)
  (*@     idx := findTID(tid, site.tids)                                      @*)
  (*@                                                                         @*)
  wp_loadField.
  iDestruct "Hactive" as "[[HactiveFrag _] _]".
  iDestruct (site_active_tids_elem_of with "HactiveAuth HactiveFrag") as "%Helem".
  rewrite -HactiveLM elem_of_list_to_set in Helem.
  apply u64_elem_of_fmap in Helem.
  wp_apply (wp_findTID tid _ tidsactiveL with "[$HactiveL]"); first done.
  iIntros (pos) "[HactiveL %Hlookup]".
  wp_pures.

  (*@     swapWithEnd(site.tids, idx)                                         @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_apply (wp_swapWithEnd with "[HactiveL]"); first by iFrame.
  iIntros (tids) "[HactiveL %Hperm]".
  wp_pures.

  (*@     site.tids = site.tids[:len(site.tids) - 1]                          @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_loadField.
  iDestruct (own_slice_wf with "HactiveL") as "%HtidsactiveCap".
  wp_apply (wp_SliceTake).
  { apply lookup_lt_Some in Hlookup. word. }
  wp_storeField.
  wp_loadField.

  (* Open GC invariant. *)
  iApply fupd_wp.
  iInv "Hinvgc" as ">HinvgcO" "HinvgcC".
  iDestruct (big_sepL_lookup_acc with "HinvgcO") as "[HinvsiteO HinvsiteC]".
  { by apply sids_all_lookup. }
  iNamed "HinvsiteO".
  (* iDestruct "HinvgcO" as (tidsM tidmin') "(HactiveAuth' & HminAuth' & %Hmin)". *)
  (* Delete [uint.nat tid] form the set of active tids. *)
  iDestruct (site_active_tids_agree with "HactiveA HactiveAuth") as %->.
  iMod (site_active_tids_delete (uint.nat tid) with "HactiveFrag HactiveA HactiveAuth") as "[HactiveA HactiveAuth]".
  (* Close GC invariant. *)
  iDestruct ("HinvsiteC" with "[HactiveA HminA]") as "HinvgcO".
  { do 3 iExists _.
    iFrame "∗ Htslb".
    iPureIntro.
    split.
    { eapply set_Forall_subseteq; last apply Hmin. set_solver. }
    { eapply set_Forall_subseteq; last apply Hmax. set_solver. }
  }
  iMod ("HinvgcC" with "[HinvgcO]") as "_"; first done.
  iModIntro.

  (*@     site.latch.Unlock()                                                 @*)
  (*@ }                                                                       @*)
  wp_apply (release_spec with "[-HΦ]").
  { iFrame "Hlock Hlocked".
    iNext.
    set idxlast := (word.sub _ _).
    iExists _, tids, _.
    iFrame "∗ #".
    assert (Hidxlast : uint.nat idxlast = length tids).
    { subst idxlast.
      rewrite (Permutation_length Hperm).
      rewrite length_delete; last done.
      assert (H : (uint.nat tidsactive.(Slice.sz) > 0)%nat).
      { rewrite -HactiveSz. apply lookup_lt_Some in Hlookup. lia. }
      rewrite HactiveSz. word.
    }
    iSplitL "HactiveL".
    { (* Prove [HactiveL]. *)
      unfold typed_slice.own_slice.
      unfold list.untype.
      iDestruct (own_slice_take_cap _ _ _ idxlast with "HactiveL") as "H".
      { rewrite fmap_length. rewrite last_length. word. }
      unfold named.
      iExactEq "H".
      rewrite -fmap_take.
      do 2 f_equal.
      replace (uint.nat idxlast) with (length tids).
      apply take_app_length.
    }
    iPureIntro.
    split.
    { (* Prove [HactiveLM]. *)
      (* Q: We're able to do this rewrite due to [fmap_Permutation] and [list_to_set_perm_L]? *)
      rewrite Hperm.
      rewrite -HactiveLM.
      set f := (λ (tid : u64), uint.nat tid).
      rewrite delete_take_drop.
      apply take_drop_middle in Hlookup.
      rewrite -{3} Hlookup.
      do 2 rewrite fmap_app.
      do 2 rewrite list_to_set_app_L.
      set s1 := (list_to_set (f <$> (take _ _))).
      rewrite list_to_set_cons.
      set s2 := (list_to_set (f <$> (drop _ _))).
      do 2 rewrite difference_union_distr_l_L.
      rewrite -Hlookup in HactiveND.
      apply NoDup_app in HactiveND as [_ [Hnotins1 Hnotins2]].
      apply NoDup_cons in Hnotins2 as [Hnotins2 _].
      assert (Hs1 : (uint.nat tid) ∉ s1).
      { intros Helem'.
        rewrite elem_of_list_to_set in Helem'.
        apply u64_elem_of_fmap in Helem'.
        set_solver.
      }
      replace (s1 ∖ {[uint.nat tid]}) with s1; last set_solver.
      assert (Hs2 : (uint.nat tid) ∉ s2).
      { intros Helem'.
        rewrite elem_of_list_to_set in Helem'.
        apply u64_elem_of_fmap in Helem'.
        set_solver.
      }
      replace (s2 ∖ {[uint.nat tid]}) with s2; last set_solver.
      set_solver.
    }
    { (* Prove [HactiveND]. *)
      rewrite Hperm.
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
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End program.
