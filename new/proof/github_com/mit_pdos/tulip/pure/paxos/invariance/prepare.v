From Perennial.program_proof.tulip.paxos Require Import prelude.

Section prepare.
  Context `{!paxos_ghostG Σ}.

  Lemma fixed_proposals_inv_prepare_term_lt psa termc' terml ds :
    let ds' := extend termc' Reject ds in
    (terml < length ds < termc')%nat ->
    free_terms_after terml (dom psa) ->
    fixed_proposals ds psa ->
    fixed_proposals ds' psa.
  Proof.
    intros ds' Horder Hfree Hfp t d Hd.
    destruct (decide (t < length ds)%nat) as [Hlt | Hge].
    { rewrite lookup_extend_l in Hd; last apply Hlt.
      by specialize (Hfp _ _ Hd).
    }
    rewrite Nat.nlt_ge in Hge.
    assert (Htlt : (t < termc')%nat).
    { apply lookup_lt_Some in Hd. rewrite extend_length in Hd. lia. }
    rewrite lookup_extend_r in Hd; last lia.
    inv Hd.
    assert (Htgt : (terml < t)%nat) by lia.
    specialize (Hfree _ Htgt).
    rewrite not_elem_of_dom in Hfree.
    by rewrite Hfree.
  Qed.

  Lemma fixed_proposals_inv_prepare_term_eq psa termc termc' ds v :
    let ds' := extend termc' Reject (ds ++ [Accept v]) in
    length ds = termc ->
    (termc < termc')%nat ->
    psa !! termc = Some v ->
    free_terms_after termc (dom psa) ->
    fixed_proposals ds psa ->
    fixed_proposals ds' psa.
  Proof.
    intros ds' Hlends Horder Hv Hfree Hfp t d Hd.
    destruct (decide (t < length ds)%nat) as [Hlt | Hge].
    { rewrite lookup_extend_l in Hd; last first.
      { rewrite last_length. lia. }
      rewrite lookup_app_l in Hd; last apply Hlt.
      by specialize (Hfp _ _ Hd).
    }
    rewrite Nat.nlt_ge in Hge.
    destruct (decide (t = length ds)) as [Heq | Hne].
    { subst t.
      rewrite Hlends Hv.
      rewrite lookup_extend_l in Hd; last first.
      { rewrite last_length. lia. }
      rewrite lookup_snoc_length in Hd.
      by inv Hd.
    }
    assert (Htgt : (length ds < t)%nat) by lia.
    assert (Htlt : (t < termc')%nat).
    { apply lookup_lt_Some in Hd. rewrite extend_length last_length in Hd. lia. }
    rewrite lookup_extend_r in Hd; last first.
    { rewrite last_length. lia. }
    inv Hd.
    specialize (Hfree _ Htgt).
    rewrite not_elem_of_dom in Hfree.
    by rewrite Hfree.
  Qed.

  Lemma latest_term_nodedec_snoc_Accept ds v :
    latest_term_nodedec (ds ++ [Accept v]) = length ds.
    rewrite /latest_term_nodedec /latest_term_before_nodedec last_length /= lookup_app_r; last done.
    by replace (_ - _)%nat with O by lia.
  Qed.

  Lemma node_inv_prepare γ nids nid wal termc terml v termc' :
    Z.of_nat termc < Z.of_nat termc' < 2 ^ 64 ->
    own_node_wal_half γ nid wal -∗
    own_current_term_half γ nid termc -∗
    own_node_ledger_half γ nid v -∗
    node_inv γ nids nid terml ==∗
    own_node_wal_half γ nid (wal ++ [CmdPaxosPrepare termc']) ∗
    own_current_term_half γ nid termc' ∗
    own_node_ledger_half γ nid v ∗
    node_inv γ nids nid terml ∗
    (if decide (is_term_of_node nid termc') then own_free_prepare_lsn γ termc' else True) ∗
    past_nodedecs_latest_before γ nid termc' terml v.
  Proof.
    iIntros (Hlt) "HwalX HtermcX Hv Hinv".
    iNamed "Hinv".
    (* Agreements. *)
    iDestruct (node_wal_agree with "HwalX Hwalnode") as %->.
    iDestruct (current_term_agree with "HtermcX Htermc") as %->.
    iDestruct (node_ledger_agree with "Hv Hlogn") as %->.
    iDestruct (accepted_proposal_lookup with "Hacpt Hpsa") as %Hv.
    (* Update the write-ahead log. *)
    set wal' := wal ++ _.
    iMod (node_wal_update wal' with "HwalX Hwalnode") as "[HwalX Hwalnode]".
    (* Obtain the free prepare LSN if [termc'] is owned by [nid]. *)
    iAssert (([∗ set] t ∈ free_termps nid termc', own_free_prepare_lsn γ t) ∗
             (if decide (is_term_of_node nid termc') then own_free_prepare_lsn γ termc' else True))%I
      with "[Hlsnps]" as "[Hlsnps Hlsnp]".
    { case_decide as Hton; last first.
      { iSplit; last done.
        iApply (big_sepS_subseteq with "Hlsnps").
        rewrite /free_termps.
        apply filter_subseteq_impl.
        intros t [Hltt Htont].
        split; [lia | done].
      }
      iDestruct (big_sepS_delete _ _ termc' with "Hlsnps") as "[Hlsnp Hlsnps]".
      { rewrite elem_of_filter.
        split; last first.
        { apply elem_of_terms_all. lia. }
        split; [lia | done].
      }
      iFrame "Hlsnp".
      iApply (big_sepS_subseteq with "Hlsnps").
      intros t Ht.
      rewrite elem_of_filter in Ht.
      destruct Ht as [[Hlet Htont] Hinall].
      rewrite elem_of_difference not_elem_of_singleton.
      split; last lia.
      rewrite elem_of_filter.
      split; last done.
      split; [lia | done].
    }
    destruct (decide (terml = termc)) as [-> | Hne]; last first.
    { (* Case: [terml < termc] iff no ledger accepted at [termc] yet. *)
      (* Update the current term [termc] to [termc']. *)
      iMod (current_term_update termc' with "HtermcX Htermc") as "[HtermcX Htermc]".
      (* Extend the node decisions [d] with [Reject]. *)
      set ds' := extend termc' Reject ds.
      iMod (past_nodedecs_update ds' with "Hds") as "Hds".
      { apply extend_prefix. }
      (* Extract a witness of the extended past decision. *)
      iDestruct (past_nodedecs_witness with "Hds") as "#Hdlb".
      (* Re-establish [fixed_proposals d' psa]. *)
      unshelve epose proof
        (fixed_proposals_inv_prepare_term_lt _ termc' _ ds _ Hdompsa Hfixed) as Hfixed'.
      { clear -Hlt Htermlc Hlends Hne. lia. }
      iFrame "∗ # %".
      iPureIntro.
      split.
      { split.
        { rewrite extend_length. lia. }
        split.
        { clear -Htermlc Hlt. lia. }
        rewrite /execute_paxos_cmds foldl_snoc /= /execute_paxos_prepare.
        by rewrite execute_paxos_cmds_unfold Hexec.
      }
      split.
      { rewrite extend_length. lia. }
      split; last first.
      { rewrite lookup_extend_l; last lia.
        unshelve epose proof (list_lookup_lt ds terml _) as [d Hd]; first lia.
        specialize (Hfixed _ _ Hd).
        rewrite Hd.
        rewrite Hfixed in Hv.
        apply nodedec_to_ledger_Some_inv in Hv.
        by rewrite Hv.
      }
      rewrite latest_term_nodedec_extend_Reject.
      unshelve epose proof (free_terms_after_latest_term_before _ _ termc _ _ Hdompsa) as Hlatest.
      { lia. }
      { done. }
      rewrite /latest_term_nodedec Hlends.
      unshelve erewrite (fixed_proposals_latest_term_before_nodedec _ _ _ _ Hfixed); [lia | done].
    }
    (* Case: [terml = termc] iff ledger [v] accepted at [termc]. *)
    (* Update the current term [termc] to [termc']. *)
    iMod (current_term_update termc' with "HtermcX Htermc") as "[HtermcX Htermc]".
    (* Snoc [Accept v] and extend the node decisions [d] with [Reject]. *)
    set ds' := extend termc' Reject (ds ++ [Accept v]).
    iMod (past_nodedecs_update ds' with "Hds") as "Hds".
    { etrans; last apply extend_prefix.
      by apply prefix_app_r.
    }
    (* Extract a witness of the extended past decision. *)
    iDestruct (past_nodedecs_witness with "Hds") as "#Hdlb".
    unshelve epose proof
      (fixed_proposals_inv_prepare_term_eq _ _ termc' _ _ Hlends _ Hv Hdompsa Hfixed) as Hfixed'.
    { lia. }
    iFrame "∗ # %".
    iPureIntro.
    split.
    { split.
      { rewrite extend_length last_length. lia. }
      split.
      { clear -Htermlc Hlt. lia. }
      rewrite /execute_paxos_cmds foldl_snoc /= /execute_paxos_prepare.
      by rewrite execute_paxos_cmds_unfold Hexec.
    }
    split.
    { rewrite extend_length length_app Hlends /=. lia. }
    split; last first.
    { rewrite lookup_extend_l; last first.
      { rewrite last_length. lia. }
      by rewrite -Hlends lookup_snoc_length.
    }
    by rewrite latest_term_nodedec_extend_Reject latest_term_nodedec_snoc_Accept.
  Qed.

  Lemma paxos_inv_prepare {γ nids nid wal termc terml v} termc' :
    nid ∈ nids ->
    Z.of_nat termc < Z.of_nat termc' < 2 ^ 64 ->
    own_node_wal_half γ nid wal -∗
    own_current_term_half γ nid termc -∗
    own_ledger_term_half γ nid terml -∗
    own_node_ledger_half γ nid v -∗
    paxos_inv γ nids ==∗
    own_node_wal_half γ nid (wal ++ [CmdPaxosPrepare termc']) ∗
    own_current_term_half γ nid termc' ∗
    own_ledger_term_half γ nid terml ∗
    own_node_ledger_half γ nid v ∗
    paxos_inv γ nids ∗
    (if decide (is_term_of_node nid termc') then own_free_prepare_lsn γ termc' else True) ∗
    past_nodedecs_latest_before γ nid termc' terml v.
  Proof.
    iIntros (Hnid Hlt) "Hwal Htermc Hterml Hv Hinv".
    iNamed "Hinv".
    rewrite -Hdomtermlm elem_of_dom in Hnid.
    destruct Hnid as [terml' Hterml'].
    iDestruct (big_sepM_lookup_acc _ _ nid with "Hnodes") as "[Hnode HnodesC]".
    { apply Hterml'. }
    iDestruct (own_ledger_term_node_inv_terml_eq with "Hterml Hnode") as %->.
    iMod (node_inv_prepare _ _ _ _ _ _ _ _ Hlt with "Hwal Htermc Hv Hnode")
      as "(Hwal & Htermc & Hv & Hnode & Hlsnp & #Hpast)".
    iDestruct ("HnodesC" with "Hnode") as "Hnodes".
    by iFrame "∗ # %".
  Qed.

End prepare.
