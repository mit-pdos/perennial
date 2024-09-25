From Perennial.program_proof.tulip.paxos Require Import prelude.

Section commit.
  Context `{!paxos_ghostG Σ}.

  Lemma equal_latest_longest_proposal_nodedec_prefix dss dsslb t v :
    map_Forall2 (λ _ dslb ds, prefix dslb ds ∧ (t ≤ length dslb)%nat) dsslb dss ->
    equal_latest_longest_proposal_nodedec dsslb t v ->
    equal_latest_longest_proposal_nodedec dss t v.
  Proof.
    rewrite /equal_latest_longest_proposal_nodedec /equal_latest_longest_proposal_with.
    rewrite -2!latest_term_before_quorum_nodedec_unfold.
    rewrite -2!longest_proposal_in_term_nodedec_unfold.
    intros Hprefixes Heq.
    case_decide as Ht; first done.
    rewrite -(latest_term_before_quorum_nodedec_prefixes _ _ _ Hprefixes).
    set t' := (latest_term_before_quorum_nodedec _ _) in Heq *.
    assert (Hlt : (t' < t)%nat).
    { by apply latest_term_before_quorum_with_lt. }
    rewrite -(longest_proposal_in_term_nodedec_prefixes dss dsslb); first apply Heq.
    apply (map_Forall2_impl _ _ _ _ Hprefixes).
    intros _ dslb ds [Hprefix Hlen].
    split; [done | lia].
  Qed.

  Lemma nodes_inv_impl_valid_base_proposals γ nids bs psb dss :
    dom bs = nids ->
    ([∗ map] t ↦ v ∈ psb, safe_base_proposal γ nids t v) -∗
    ([∗ map] nid ↦ ds; psa ∈ dss; bs, node_inv_ds_psa γ nid ds psa) -∗
    ⌜valid_base_proposals bs psb⌝.
  Proof.
    iIntros (Hdombs) "Hsafe Hinv".
    iIntros (t v Hv).
    iDestruct (big_sepM_lookup with "Hsafe") as "Hsafe"; first apply Hv.
    iNamed "Hsafe".
    rewrite /valid_base_proposal.
    rewrite big_sepM2_alt.
    iDestruct "Hinv" as "[%Hdomdss Hinv]".
    iDestruct (big_sepM_dom_subseteq_difference _ _ (dom dssqlb) with "Hinv") as "Hm".
    { rewrite dom_map_zip_with_L Hdomdss intersection_idemp Hdombs.
      by destruct Hquorum as [Hincl _].
    }
    iDestruct "Hm" as (m [Hdomm Hinclm]) "[Hm _]".
    set dssq := fst <$> m.
    set bsq := snd <$> m.
    iExists bsq.
    iAssert (⌜map_Forall2 (λ _ dslb ds, prefix dslb ds ∧ (t ≤ length dslb)%nat) dssqlb dssq⌝)%I
      as %Hprefix.
    { iIntros (x).
      destruct (dssqlb !! x) as [dslb |] eqn:Hdslb, (dssq !! x) as [ds |] eqn:Hds; last first.
      { done. }
      { rewrite -not_elem_of_dom -Hdomm not_elem_of_dom in Hdslb.
        subst dssq.
        by rewrite lookup_fmap Hdslb /= in Hds.
      }
      { subst dssq.
        by rewrite -not_elem_of_dom dom_fmap_L Hdomm not_elem_of_dom Hdslb in Hds.
      }
      simpl.
      iDestruct (big_sepM_lookup with "Hdsq") as "Hdsqx"; first apply Hdslb.
      rewrite lookup_fmap_Some in Hds.
      destruct Hds as ([ds' psa] & Hds & Hmx). simpl in Hds. subst ds'.
      iDestruct (big_sepM_lookup with "Hm") as "Hinv"; first apply Hmx.
      iNamed "Hinv". simpl.
      iDestruct (past_nodedecs_prefix with "Hdsqx Hpastd") as %Hprefix.
      by specialize (Hlen _ _ Hdslb).
    }
    pose proof (equal_latest_longest_proposal_nodedec_prefix _ _ _ _ Hprefix Heq) as Heq'.
    iAssert (⌜map_Forall2 (λ _ ds psa, fixed_proposals ds psa ∧ (t ≤ length ds)%nat) dssq bsq⌝)%I
      as %Hfixed.
    { iIntros (x).
      destruct (dssq !! x) as [ds |] eqn:Hds, (bsq !! x) as [psa |] eqn:Hpsa; last first.
      { done. }
      { rewrite -not_elem_of_dom dom_fmap_L in Hds.
        apply elem_of_dom_2 in Hpsa.
        by rewrite dom_fmap_L in Hpsa.
      }
      { rewrite -not_elem_of_dom dom_fmap_L in Hpsa.
        apply elem_of_dom_2 in Hds.
        by rewrite dom_fmap_L in Hds.
      }
      simpl.
      iDestruct (big_sepM_lookup _ _ x (ds, psa) with "Hm") as "Hinv".
      { rewrite lookup_fmap_Some in Hds.
        destruct Hds as ([ds1 psa1] & Hds & Hmx1). simpl in Hds. subst ds1.
        rewrite lookup_fmap_Some in Hpsa.
        destruct Hpsa as ([ds2 psa2] & Hpsa & Hmx2). simpl in Hpsa. subst psa2.
        rewrite Hmx1 in Hmx2.
        by inv Hmx2.
      }
      iNamed "Hinv".
      specialize (Hprefix x).
      assert (is_Some (dssqlb !! x)) as [dslb Hdslb].
      { rewrite -elem_of_dom -Hdomm elem_of_dom.
        apply lookup_fmap_Some in Hds as (dp & _ & Hinv).
        done.
      }
      rewrite Hds Hdslb /= in Hprefix.
      iPureIntro.
      split; first apply Hfixed.
      destruct Hprefix as [Hprefix Hlelen].
      apply prefix_length in Hprefix.
      lia.
    }
    iPureIntro.
    split.
    { subst bsq.
      trans (snd <$> map_zip dss bs).
      { by apply map_fmap_mono. }
      rewrite snd_map_zip; first done.
      intros x Hbsx.
      by rewrite -elem_of_dom -Hdomdss elem_of_dom in Hbsx.
    }
    split.
    { subst bsq.
      rewrite dom_fmap_L Hdomm Hdombs.
      by destruct Hquorum as [_ Hquorum].
    }
    by eapply fixed_proposals_equal_latest_longest_proposal_nodedec.
  Qed.

  Lemma nodes_inv_impl_valid_lb_ballots γ bs psb :
    own_base_proposals γ psb -∗
    ([∗ map] nid ↦ psa ∈ bs, node_inv_psa γ nid psa) -∗
    ⌜valid_lb_ballots bs psb⌝.
  Proof.
    iIntros "Hpsb Hinv".
    iIntros (nid psa Hpsa).
    iDestruct (big_sepM_lookup with "Hinv") as "Hinv"; first apply Hpsa.
    iNamed "Hinv".
    iIntros (t v Hv).
    iDestruct (big_sepM_lookup with "Hpsalbs") as (vlb) "[Hvlb %Hprefix]"; first apply Hv.
    iDestruct (base_proposal_lookup with "Hvlb Hpsb") as %Hvlb.
    by eauto.
  Qed.

  Lemma nodes_inv_impl_valid_ub_ballots γ bs ps :
    own_proposals γ ps -∗
    ([∗ map] nid ↦ psa ∈ bs, node_inv_psa γ nid psa) -∗
    ⌜valid_ub_ballots bs ps⌝.
  Proof.
    iIntros "Hps Hinv".
    iIntros (nid psa Hpsa).
    iDestruct (big_sepM_lookup with "Hinv") as "Hinv"; first apply Hpsa.
    iNamed "Hinv".
    iIntros (t v Hv).
    iDestruct (big_sepM_lookup with "Hpsaubs") as (vlb) "[Hvub %Hprefix]"; first apply Hv.
    iDestruct (proposal_prefix with "Hvub Hps") as %(vub & Hvub & Hprefixvlb).
    iPureIntro.
    exists vub.
    split; first apply Hvub.
    by trans vlb.
  Qed.

  Lemma node_inv_extract_ds_psa γ nid terml :
    node_inv γ nid terml -∗
    ∃ ds psa, node_inv_without_ds_psa γ nid terml ds psa ∗
              node_inv_ds_psa γ nid ds psa.
  Proof. iIntros "Hinv". iNamed "Hinv". iFrame "∗ # %". Qed.

  Lemma nodes_inv_extract_ds_psa γ termlm :
    ([∗ map] nid ↦ terml ∈ termlm, node_inv γ nid terml) -∗
    ∃ dss bs, ([∗ map] nid ↦ terml; dp ∈ termlm; map_zip dss bs,
                 node_inv_without_ds_psa γ nid terml dp.1 dp.2) ∗
              ([∗ map] nid ↦ ds; psa ∈ dss; bs, node_inv_ds_psa γ nid ds psa).
  Proof.
    iIntros "Hinvs".
    set Φ := (λ nid terml dp,
                node_inv_without_ds_psa γ nid terml dp.1 dp.2 ∗
                node_inv_ds_psa γ nid dp.1 dp.2)%I.
    iDestruct (big_sepM_sepM2_exists Φ termlm with "[Hinvs]") as (dpm) "Hdpm".
    { iApply (big_sepM_mono with "Hinvs").
      iIntros (nid terml Hterml) "Hinv".
      subst Φ.
      iNamed "Hinv".
      iExists (ds, psa).
      iFrame "∗ # %".
    }
    iDestruct (big_sepM2_dom with "Hdpm") as %Hdom.
    subst Φ.
    iNamed "Hdpm".
    iDestruct (big_sepM2_sep with "Hdpm") as "[Hinv Hdp]".
    iExists (fst <$> dpm), (snd <$> dpm).
    rewrite map_zip_fst_snd.
    iFrame "Hinv".
    iDestruct (big_sepM2_flip with "Hdp") as "Hdp".
    rewrite -big_sepM_big_sepM2; last apply Hdom.
    rewrite big_sepM2_alt map_zip_fst_snd.
    iFrame "Hdp".
    iPureIntro.
    by rewrite 2!dom_fmap_L.
  Qed.

  Lemma nodes_inv_merge_ds_psa γ termlm dss bs :
    ([∗ map] nid ↦ terml; dp ∈ termlm; map_zip dss bs,
       node_inv_without_ds_psa γ nid terml dp.1 dp.2) -∗
    ([∗ map] nid ↦ ds; psa ∈ dss; bs, node_inv_ds_psa γ nid ds psa) -∗
    ([∗ map] nid ↦ terml ∈ termlm, node_inv γ nid terml).
  Proof.
    iIntros "Hinv Hdp".
    iDestruct (big_sepM2_alt with "Hdp") as "[%Hdom Hdp]".
    iDestruct (big_sepM2_dom with "Hinv") as %Hdomtermlm.
    iDestruct (big_sepM_big_sepM2_1 with "Hdp") as "Hdp".
    { apply Hdomtermlm. }
    rewrite big_sepM2_flip.
    iCombine "Hinv Hdp" as "Hinv".
    rewrite -big_sepM2_sep.
    iApply (big_sepM2_sepM_impl with "Hinv").
    { apply Hdomtermlm. }
    iIntros (nid dp terml terml' Hdp Hterml Hterml') "!> [Hinv Hdp]".
    rewrite Hterml in Hterml'. symmetry in Hterml'. inv Hterml'.
    iNamed "Hinv".
    iNamed "Hdp".
    iNamed "Hpsa".
    iFrame "∗ # %".
  Qed.

  Lemma nodes_inv_safe_ledger_in_impl_chosen_in γ nids bs t v :
    dom bs = nids ->
    safe_ledger_in γ nids t v -∗
    ([∗ map] nid ↦ psa ∈ bs, node_inv_psa γ nid psa) -∗
    ⌜chosen_in bs t v⌝.
  Proof.
    iIntros (Hdombs) "#Hsafe Hinv".
    iNamed "Hsafe".
    set bsq := (filter (λ x, x.1 ∈ nidsq) bs).
    iExists bsq.
    rewrite base.and_assoc.
    iSplit.
    { iPureIntro.
      split; first apply map_filter_subseteq.
      rewrite Hdombs.
      subst bsq.
      destruct Hquorum as [Hincl Hquorum].
      rewrite (dom_filter_L _ _ nidsq); first apply Hquorum.
      intros nidx.
      split; last by intros (ps & _ & Hin).
      intros Hin.
      assert (is_Some (bs !! nidx)) as [ps Hps].
      { rewrite -elem_of_dom Hdombs. set_solver. }
      by exists ps.
    }
    iIntros (nid' ps Hps).
    iDestruct (big_sepS_elem_of _ _ nid' with "Hacpt") as "Hvacpt'".
    { by apply map_lookup_filter_Some_1_2 in Hps. }
    iDestruct "Hvacpt'" as (v') "[Hvacpt' %Hlen]".
    iDestruct (node_inv_is_accepted_proposal_lb_impl_prefix with "Hvacpt Hvacpt' Hinv") as %Hprefix.
    { by rewrite -Hdombs in Hmember. }
    { apply elem_of_dom_2 in Hps.
      apply (elem_of_weaken _ (dom bsq)); first done.
      apply dom_filter_subseteq.
    }
    assert (Hvv' : prefix v v').
    { destruct Hprefix as [Hprefix | Hprefix]; first apply Hprefix.
      by rewrite (prefix_length_eq _ _ Hprefix Hlen).
    }
    iDestruct (accepted_proposal_lb_weaken v with "Hvacpt'") as "Hlb"; first apply Hvv'.
    iDestruct (big_sepM_lookup with "Hinv") as "Hnode".
    { eapply lookup_weaken; [apply Hps | apply map_filter_subseteq]. }
    iNamed "Hnode".
    iDestruct (accepted_proposal_prefix with "Hvacpt' Hpsa") as %(va & Hva & Hprefixva).
    iPureIntro.
    exists va.
    split; first apply Hva.
    by trans v'.
  Qed.

  Lemma nodes_inv_safe_ledger_impl_chosen γ nids bs v :
    dom bs = nids ->
    safe_ledger γ nids v -∗
    ([∗ map] nid ↦ psa ∈ bs, node_inv_psa γ nid psa) -∗
    ⌜chosen bs v⌝.
  Proof.
    iIntros (Hdombs) "[%t #Hsafe] Hinv".
    iExists t.
    by iApply (nodes_inv_safe_ledger_in_impl_chosen_in with "Hsafe Hinv").
  Qed.

  Lemma nodes_inv_ds_psa_impl_nodes_inv_psa γ dss bs :
    ([∗ map] nid ↦ ds; psa ∈ dss; bs, node_inv_ds_psa γ nid ds psa) -∗
    ([∗ map] nid ↦ psa ∈ bs, node_inv_psa γ nid psa). 
  Proof.
    iIntros "Hpds".
    rewrite big_sepM2_flip.
    iApply (big_sepM2_sepM_impl with "Hpds"); first done.
    iIntros (nid psa ds psa' Hpsa Hds Hpsa') "!> Hpd".
    rewrite Hpsa in Hpsa'. symmetry in Hpsa'. inv Hpsa'.
    by iNamed "Hpd".
  Qed.

  Lemma paxos_inv_commit γ nids logi' :
    safe_ledger γ nids logi' -∗
    paxos_inv γ nids ==∗
    paxos_inv γ nids ∗
    is_internal_log_lb γ logi'.
  Proof.
    iIntros "#Hsafe Hinv".
    iNamed "Hinv".
    (* Extract past decisions and accepted proposals from the node invariant. *)
    iDestruct (nodes_inv_extract_ds_psa with "Hnodes") as (dss bs) "[Hnodes Hpds]".
    iDestruct (big_sepM2_dom with "Hpds") as %Hdompds.
    iDestruct (big_sepM2_dom with "Hnodes") as %Hdombs.
    rewrite dom_map_zip_with_L Hdompds Hdomtermlm in Hdombs. symmetry in Hdombs.
    replace (_ ∩ _) with (dom bs) in Hdombs by set_solver.
    (* not sure why the following fails, so using replace above as a workaround *)
    (* rewrite intersection_idemp in Hdombs. *)
    (* Obtain [valid_base_proposals bs psb]. *)
    iDestruct (nodes_inv_impl_valid_base_proposals with "Hsafepsb Hpds") as %Hvbp.
    { apply Hdombs. }
    (* Obtain [valid_lb_ballots bs psb]. *)
    iDestruct (nodes_inv_impl_valid_lb_ballots _ bs with "Hpsb [Hpds]") as %Hvlb.
    { by iApply nodes_inv_ds_psa_impl_nodes_inv_psa. }
    (* Obtain [valid_ub_ballots bs ps]. *)
    iDestruct (nodes_inv_impl_valid_ub_ballots _ bs with "Hps [Hpds]") as %Hvub.
    { by iApply nodes_inv_ds_psa_impl_nodes_inv_psa. }
    (* Finally, derive [consistency bs]. *)
    pose proof (vlb_vub_vbp_vp_impl_consistency _ _ _ Hvlb Hvub Hvbp Hvp) as Hcst.
    (* Now, derive [chosen bs logi] and [chosen bs logi']. *)
    iDestruct (nodes_inv_safe_ledger_impl_chosen _ _ bs with "Hsafelogi [Hpds]") as %Hchosen.
    { apply Hdombs. }
    { by iApply nodes_inv_ds_psa_impl_nodes_inv_psa. }
    iDestruct (nodes_inv_safe_ledger_impl_chosen _ _ bs with "Hsafe [Hpds]") as %Hchosen'.
    { apply Hdombs. }
    { by iApply nodes_inv_ds_psa_impl_nodes_inv_psa. }
    (* Derive [prefix logi logi' ∨ prefix logi' logi]. *)
    specialize (Hcst _ _ Hchosen Hchosen').
    (* Merge [node_inv_ds_psa] back. *)
    iDestruct (nodes_inv_merge_ds_psa with "Hnodes Hpds") as "Hnodes".
    destruct Hcst as [Hge | Hle]; last first.
    { (* Case: The old log is at least as long as the new log. Simply extract a witness. *)
      iDestruct (internal_log_witness logi' with "Hlogi") as "#Hlb"; first apply Hle.
      by iFrame "∗ # %".
    }
    (* Case: The new log is at least as long as the old log. Update the log. *)
    iMod (internal_log_update with "Hlogi") as "Hlogi"; first apply Hge.
    iDestruct (internal_log_witness logi' with "Hlogi") as "#Hlb"; first done.
    by iFrame "∗ # %".
  Qed.

End commit.
