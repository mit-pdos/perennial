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

  Lemma free_terms_after_latest_term_before psa t1 t2 :
    (t1 < t2)%nat ->
    is_Some (psa !! t1) ->
    free_terms_after t1 (dom psa) ->
    latest_term_before t2 psa = t1.
  Proof.
    intros Hlt Hsome Hfree.
    induction t2 as [| t IH]; first lia.
    rewrite /latest_term_before /=.
    destruct (decide (t = t1)) as [-> | Hne].
    { destruct Hsome as [v Hv]. by rewrite Hv. }
    assert (Ht1 : (t1 < t)%nat) by lia.
    rewrite /latest_term_before in IH.
    specialize (Hfree _ Ht1).
    rewrite not_elem_of_dom in Hfree.
    by rewrite Hfree (IH Ht1).
  Qed.

  Lemma node_inv_prepare γ nid termc termc' terml v :
    (termc < termc')%nat ->
    own_current_term_half γ nid termc -∗
    own_node_ledger_half γ nid v -∗
    node_inv γ nid terml ==∗
    own_current_term_half γ nid termc' ∗
    own_node_ledger_half γ nid v ∗
    node_inv γ nid terml ∗
    past_nodedecs_latest_before γ nid termc' terml v.
  Proof.
    iIntros (Hlt) "HtermcX Hv Hinv".
    iNamed "Hinv".
    iDestruct (current_term_agree with "HtermcX Htermc") as %->.
    iDestruct (node_ledger_agree with "Hv Hlogn") as %->.
    iDestruct (accepted_proposal_lookup with "Hacpt Hpsa") as %Hv.
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
      { rewrite extend_length. lia. }
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
      (fixed_proposals_inv_prepare_term_eq _ _ _ _ _ Hlends Hlt Hv Hdompsa Hfixed) as Hfixed'.
    iFrame "∗ # %".
    iPureIntro.
    split.
    { rewrite extend_length last_length. lia. }
    split.
    { rewrite extend_length length_app Hlends /=. lia. }
    split; last first.
    { rewrite lookup_extend_l; last first.
      { rewrite last_length. lia. }
      by rewrite -Hlends lookup_snoc_length.
    }
    by rewrite latest_term_nodedec_extend_Reject latest_term_nodedec_snoc_Accept.
  Qed.

  Lemma paxos_inv_prepare {γ nids nid termc terml v} termc' :
    nid ∈ nids ->
    (termc < termc')%nat ->
    own_current_term_half γ nid termc -∗
    own_ledger_term_half γ nid terml -∗
    own_node_ledger_half γ nid v -∗
    paxos_inv γ nids ==∗
    own_current_term_half γ nid termc' ∗
    own_ledger_term_half γ nid terml ∗
    own_node_ledger_half γ nid v ∗
    paxos_inv γ nids ∗
    past_nodedecs_latest_before γ nid termc' terml v.
  Proof.
    iIntros (Hnid Hlt) "Htermc Hterml Hv Hinv".
    iNamed "Hinv".
    rewrite -Hdomtermlm elem_of_dom in Hnid.
    destruct Hnid as [terml' Hterml'].
    iDestruct (big_sepM_lookup_acc _ _ nid with "Hnodes") as "[Hnode HnodesC]".
    { apply Hterml'. }
    iDestruct (own_ledger_term_node_inv_terml_eq with "Hterml Hnode") as %->.
    iMod (node_inv_prepare _ _ _ _ _ _ Hlt with "Htermc Hv Hnode")
      as "(Htermc & Hv & Hnode & #Hpast)".
    iDestruct ("HnodesC" with "Hnode") as "Hnodes".
    by iFrame "∗ # %".
  Qed.

End prepare.
