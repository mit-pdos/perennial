From Perennial.program_proof.mvcc Require Import txnsite_prelude.
From Perennial.program_proof.mvcc Require Import txnsite_repr tid_proof.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem wp_TxnSite__GetSafeTS site (sid : u64) γ :
  is_txnsite site sid γ -∗
  {{{ True }}}
    TxnSite__GetSafeTS #site
  {{{ (tid : u64), RET #tid; site_min_tid_lb γ sid (uint.nat tid) }}}.
Proof.
  iIntros "#Hsite" (Φ) "!> _ HΦ".
  iNamed "Hsite".
  wp_rec. wp_pures.
  
  (*@ func (site *TxnSite) GetSafeTS() uint64 {                               @*)
  (*@     site.latch.Lock()                                                   @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked HsiteOwn]".
  iNamed "HsiteOwn".
  iDestruct (typed_slice.own_slice_sz with "HactiveL") as "%HtidsactiveSz".
  wp_pures.

  (*@     var tidnew uint64                                                   @*)
  (*@     tidnew = tid.GenTID(site.sid)                                       @*)
  (*@                                                                         @*)
  wp_apply wp_ref_of_zero; first done.
  iIntros (tidRef) "HtidRef".
  wp_pures.
  wp_loadField.
  wp_apply (wp_GenTID with "Hinvtid Hsidtok").
  { done. }
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
  (* Give atomic precondition. *)
  iExists _. iFrame "Hts".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iIntros "%tsnew (Htsnew & %Hlt)". rename ts into tsold.
  (* Update the minimal TID to the smallest among [{[ tsnew ]} ∪ tidsactiveM]. *)
  set tids := {[ tsnew ]} ∪ tidsactiveM.
  assert (∃ tidmin', set_Forall (λ tid, (tidmin' ≤ tid)%nat) tids ∧ tidmin' ∈ tids)
    as (tidmin' & Htidmin' & Helem).
  { destruct (minimal_exists_elem_of_L Nat.le tids) as (tidx & Htidx & Hminimal); first set_solver.
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
  iClear "Htslb".
  iDestruct (ts_witness with "Htsnew") as "#Htslb".
  iMod "Hclose" as "_".
  (* Close the GC invariant. *)
  iDestruct ("HinvsiteC" with "[HactiveA HminA]") as "HinvsiteO".
  { iExists _, _, tsnew.
    iFrame "∗ Htslb".
    iPureIntro.
    split.
    { eapply set_Forall_subseteq; last apply Htidmin'. set_solver. }
    { (* apply set_Forall_union_inv_1 in Hmax as Hminmax.
      rewrite set_Forall_singleton in Hminmax. *)
      apply set_Forall_union.
      { rewrite set_Forall_singleton.
        apply set_Forall_union_inv_1 in Htidmin'.
        rewrite set_Forall_singleton in Htidmin'. lia.
      }
      { apply set_Forall_union_inv_2 in Hmax.
        eapply set_Forall_impl; first apply Hmax.
        intros. word.
      }
    }
  }
  iMod ("HinvgcC" with "HinvsiteO") as "_".
  iDestruct ("HinvtsC" with "[] Htsnew") as "HinvsstO".
  { iPureIntro. lia. }
  iMod ("HinvsstC" with "HinvsstO") as "_".
  iModIntro.
  iIntros (tidnew) "[%Etidnew Hsidtok]".
  subst tsnew.
  wp_store.
  
  (*@     machine.Assume(tidnew < 18446744073709551615)                       @*)
  (*@                                                                         @*)
  wp_load.
  wp_apply wp_Assume.
  iIntros (Hoverflow).
  apply bool_decide_eq_true_1 in Hoverflow.
  
  (*@     var tidmin uint64 = tidnew                                          @*)
  (*@                                                                         @*)
  wp_load.
  wp_apply (wp_ref_to); first by auto.
  iIntros (tidminRef) "HtidminRef".
  wp_pures.

  (*@     for _, tid := range site.tids {                                     @*)
  (*@         if tid < tidmin {                                               @*)
  (*@             tidmin = tid                                                @*)
  (*@         }                                                               @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  set u64_to_nat := (λ x : u64, uint.nat x).
  iDestruct (own_slice_small_acc with "HactiveL") as "[HactiveS HactiveC]".
  wp_loadField.
  set P := λ (i : u64), (∃ (tidloop : u64), let tids := tidnew :: (take (uint.nat i) tidsactiveL) in
    "HtidminRef" ∷ tidminRef ↦[uint64T] #tidloop ∗
    "%Helem'" ∷ ⌜tidloop ∈ tids⌝ ∗
    "%Htidloop" ∷ (⌜Forall (λ tid, (uint.nat tidloop ≤ tid)%nat) (u64_to_nat <$> tids)⌝))%I.
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
      do 2 replace (uint.nat (word.add i 1)) with (S (uint.nat i)) by word.
      rewrite (take_S_r _ _ tidx); last done.
      iSplit; iPureIntro.
      { set_solver. }
      { rewrite app_comm_cons fmap_app.
        rewrite Forall_app.
        split.
        { apply (Forall_impl _ _ _ Htidloop). intros. word. }
        apply Forall_singleton. done.
      }
    - iApply "HΦ".
      iModIntro.
      iExists _.
      iFrame.
      do 2 replace (uint.nat (word.add i 1)) with (S (uint.nat i)) by word.
      rewrite (take_S_r _ _ tidx); last done.
      iSplit; iPureIntro.
      { set_solver. }
      { rewrite app_comm_cons fmap_app.
        rewrite Forall_app.
        split.
        { apply (Forall_impl _ _ _ Htidloop). intros. word. }
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
  
  (*@     site.latch.Unlock()                                                 @*)
  (*@                                                                         @*)
  iDestruct ("HactiveC" with "HactiveS") as "HactiveL".
  wp_loadField.
  wp_apply (wp_Mutex__Unlock with "[-HΦ HtidminRef]").
  { eauto 10 with iFrame. }
  wp_pures.

  (*@     return tidmin                                                       @*)
  (*@ }                                                                       @*)
  (* Deduce [tidmin' = tidloop]. *)
  rewrite -HtidsactiveSz firstn_all in Htidloop Helem'.
  replace tidmin' with (uint.nat tidloop); last first.
  { subst tids tidsactiveM.
    clear -Helem Htidmin' Helem' Htidloop.
    rewrite -list_to_set_cons elem_of_list_to_set in Helem.
    rewrite -list_to_set_cons set_Forall_list_to_set in Htidmin'.
    replace (uint.nat tidnew) with (u64_to_nat tidnew) in Helem, Htidmin'; last done.
    rewrite -fmap_cons in Helem Htidmin'.
    apply (list_elem_of_fmap_2 u64_to_nat) in Helem'.
    rewrite Forall_forall in Htidmin'.
    rewrite Forall_forall in Htidloop.
    apply Htidmin' in Helem'.
    apply Htidloop in Helem.
    subst u64_to_nat. word.
  }
  wp_load.
  by iApply "HΦ".
Qed.

End program.
