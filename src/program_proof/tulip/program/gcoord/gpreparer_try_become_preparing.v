From Perennial.program_proof.tulip.invariance Require Import propose.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import count_bool_map.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gpreparer_repr gpreparer_cquorum gpreparer_hcquorum.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupPreparer__tryBecomePreparing (gpp : loc) ts gid γ :
    gid ∈ gids_all ->
    know_tulip_inv γ -∗
    {{{ own_gpreparer_with_phase gpp GPPValidating ts gid γ }}}
      GroupPreparer__tryBecomePreparing #gpp
    {{{ (resend : bool), RET #resend; own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros (Hgid) "#Hinv".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) tryBecomePreparing() {                        @*)
    (*@     // Count how many replicas have validated.                          @*)
    (*@     nvd := uint64(len(gpp.vdm))                                         @*)
    (*@     if !gpp.cquorum(nvd) {                                              @*)
    (*@         // Cannot move to the PREPARING phase unless some classic quorum of @*)
    (*@         // replicas successfully validate.                              @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hgpp". iNamed "Hvdm".
    wp_loadField.
    wp_apply (wp_MapLen with "Hvdm").
    iIntros "[%Hnvdmnoof Hvdm]".
    iAssert (own_gpreparer_vdm gpp ts gid γ)%I with "[HvdmP Hvdm]" as "Hvdm".
    { iFrame "∗ # %". }
    wp_apply (wp_GroupPreparer__cquorum with "Hnrps").
    iIntros "Hnrps".
    case_bool_decide as Hnvd; wp_pures; last first.
    { iApply "HΦ". by iFrame "∗ #". }

    (*@     // Count how many replicas have responded in the fast path.         @*)
    (*@     nresp := uint64(len(gpp.frespm))                                    @*)
    (*@     if !gpp.cquorum(nresp) {                                            @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hfrespm".
    wp_loadField.
    wp_apply (wp_MapLen with "Hfrespm").
    iIntros "[%Hnrespmnoof Hfrespm]".
    wp_apply (wp_GroupPreparer__cquorum with "Hnrps").
    iIntros "Hnrps".
    case_bool_decide as Hnresp; wp_pures; last first.
    { iApply "HΦ". by iFrame "∗ # %". }

    (*@     // Count how many replicas have prepared.                           @*)
    (*@     nfp := util.CountBoolMap(gpp.frespm, true)                          @*)
    (*@     if !gpp.hcquorum(nfp) {                                             @*)
    (*@         // Cannot move to the PREPARING phase unless half (i.e., celing(n / 2)) @*)
    (*@         // of replicas in some classic quorum agrees to prepare.        @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_CountBoolMap with "Hfrespm").
    iIntros (nfp) "[Hfrespm %Hnfp]".
    wp_apply (wp_GroupPreparer__hcquorum with "Hnrps").
    iIntros "Hnrps".
    case_bool_decide as Hhcq; wp_pures; last first.
    { iApply "HΦ". by iFrame "∗ # %". }
    (* Prove [safe_proposal γ gid ts 1%nat true] to propose [true] at rank 1 for [ts]. *)
    iAssert (safe_proposal γ gid ts 1%nat true)%I as "#Hsafepsl".
    { simpl.
      iDestruct (big_sepM_sep with "Hfast") as "[Hpdecx _]".
      rewrite /is_replica_pdec_at_rank.
      iDestruct (big_sepM_exists_sepM2 with "Hpdecx") as (bm) "Hpdecy".
      iDestruct (big_sepM2_and with "Hpdecy") as "[Hpdec Hacpt]".
      iDestruct (big_sepM2_pure with "Hacpt") as %[_ Hacpt].
      iDestruct (big_sepM2_dom with "Hpdec") as %Hdombm.
      assert (Hcq : cquorum rids_all (dom bm)).
      { rewrite -Hdombm.
        split; first apply Hfincl.
        rewrite /cquorum_size size_dom.
        clear -Hnresp. word.
      }
      iExists bm.
      set sc := size rids_all.
      simpl.
      assert (latest_before_quorum 1 bm = O) as ->.
      { unshelve epose proof (latest_before_quorum_lt bm 1%nat _ _) as Hltone.
        { rewrite -dom_empty_iff_L. by eapply cquorum_non_empty_q. }
        { done. }
        lia.
      }
      iSplit.
      { iApply (big_sepM2_sepM_impl with "Hpdec"); first done.
        iIntros (rid b l1 l2 Hb Hl1 Hl2) "!> #Hlb".
        rewrite Hl1 in Hl2. by inv Hl2.
      }
      iSplit; first done.
      iPureIntro.
      split; first apply Hcq.
      split.
      { intros k l Hl.
        assert (is_Some (frespm !! k)) as [b Hb].
        { by rewrite -elem_of_dom Hdombm elem_of_dom. }
        specialize (Hacpt _ _ _ Hb Hl).
        apply lookup_lt_Some in Hacpt.
        clear -Hacpt. lia.
      }
      simpl.
      assert (Heq : (uint.nat nfp ≤ nfast bm true)%nat).
      { rewrite Hnfp /nfast -2!size_dom.
        apply subseteq_size.
        intros x Hx.
        apply elem_of_dom in Hx as [b Hb].
        apply map_lookup_filter_Some in Hb as [Hb Heq].
        simpl in Heq. subst b.
        assert (is_Some (bm !! x)) as [l Hl].
        { by rewrite -elem_of_dom -Hdombm elem_of_dom. }
        specialize (Hacpt _ _ _ Hb Hl).
        apply elem_of_dom.
        exists l.
        by apply map_lookup_filter_Some.
      }
      clear -Hhcq Heq. word.
    }

    (*@     gpp.srespm = make(map[uint64]bool)                                  @*)
    (*@     gpp.phase = GPP_PREPARING                                           @*)
    (*@                                                                         @*)
    iNamed "Hsrespm".
    wp_apply wp_NewMap.
    iClear "Hsrespm".
    iIntros (srespmP') "Hsrespm".
    wp_storeField.
    iNamed "Hphase".
    simpl.
    wp_storeField.
    iAssert (own_gpreparer_frespm gpp ts gid γ)%I
      with "[HfrespmP Hfrespm]" as "Hfrespm".
    { iFrame "∗ # %". }
    iAssert (own_gpreparer_phase gpp GPPPreparing)%I
      with "[HphaseP]" as "Hphase".
    { by iFrame. }
    iAssert (own_gpreparer_srespm gpp GPPPreparing ts gid γ)%I
      with "[HsrespmP Hsrespm]" as "Hsrespm".
    { iFrame. by rewrite /= dom_empty_L big_sepS_empty. }

    (*@     // Logical action: Propose.                                         @*)
    (*@ }                                                                       @*)
    iNamed "Hinv".
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    simpl.
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
    { apply Hgid. }
    iMod (group_inv_propose with "Hsafepsl [Htxncli] Hgroup") as "[Hgroup #Hppsl]".
    { done. }
    { by rewrite /exclusive_proposal /=. }
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    iApply "HΦ".
    iFrame "∗ #".
    iPureIntro.
    split; first apply Hvincl.
    rewrite /cquorum_size size_dom.
    clear -Hnvd. word.
  Qed.

End program.
