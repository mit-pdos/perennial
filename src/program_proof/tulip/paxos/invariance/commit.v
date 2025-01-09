From Perennial.program_proof.tulip.paxos Require Import prelude.

Section commit.
  Context `{!paxos_ghostG Σ}.

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

  Lemma safe_ledger_log_impl_prefix γ nids v v' :
    safe_ledger γ nids v' -∗
    own_log_half γ v -∗
    paxos_inv γ nids -∗
    ⌜prefix v v' ∨ prefix v' v⌝.
  Proof.
    iIntros "#Hsafe Hloguser Hinv".
    iNamed "Hinv".
    (* Agreement on the log content. *)
    iDestruct (log_agree with "Hloguser Hlog") as %->.
    (* Extract past decisions and accepted proposals from the node invariant. *)
    iDestruct (nodes_inv_extract_ds_psa with "Hnodes") as (dss bs) "[Hnodes Hpds]".
    iDestruct (big_sepM2_dom with "Hpds") as %Hdompds.
    iDestruct (big_sepM2_dom with "Hnodes") as %Hdombs.
    rewrite dom_map_zip_with_L Hdompds Hdomtermlm intersection_idemp_L in Hdombs.
    symmetry in Hdombs.
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
    iDestruct (nodes_inv_safe_ledger_impl_chosen _ _ bs with "Hsafelog [Hpds]") as %Hchosen.
    { apply Hdombs. }
    { by iApply nodes_inv_ds_psa_impl_nodes_inv_psa. }
    iDestruct (nodes_inv_safe_ledger_impl_chosen _ _ bs with "Hsafe [Hpds]") as %Hchosen'.
    { apply Hdombs. }
    { by iApply nodes_inv_ds_psa_impl_nodes_inv_psa. }
    (* Derive [prefix logi logi' ∨ prefix logi' logi]. *)
    by specialize (Hcst _ _ Hchosen Hchosen').
  Qed.

  Lemma paxos_inv_commit {γ nids nid vcli vnode} vsafe :
    nid ∈ nids ->
    prefix vsafe vnode ->
    safe_ledger γ nids vsafe -∗
    own_log_half γ vcli -∗
    own_node_ledger_half γ nid vnode -∗
    paxos_inv γ nids ==∗
    (∃ vcli', own_log_half γ vcli' ∧ ⌜prefix vsafe vcli'⌝) ∗
    own_node_ledger_half γ nid vnode ∗
    paxos_inv γ nids.
  Proof.
    iIntros (Hnid Hprefix) "#Hsafe Hlogcli HlognX Hinv".
    iDestruct (safe_ledger_log_impl_prefix with "Hsafe Hlogcli Hinv") as %Horprefix.
    destruct Horprefix as [Hext | Hnoext]; last first.
    { (* Case: The global log is longer than the committed log on [nid]. No update required. *)
      by iFrame.
    }
    (* Case: The global log is shorted. Extend it to [vsafe]. *)
    iNamed "Hinv".
    iDestruct (log_agree with "Hlogcli Hlog") as %->.
    iAssert (⌜cpool_subsume_log vsafe cpool⌝)%I as %Hsubsume.
    { rewrite -Hdomtermlm elem_of_dom in Hnid.
      destruct Hnid as [terml Hterml].
      iDestruct (big_sepM_lookup with "Hnodes") as "Hnode"; first apply Hterml.
      iNamed "Hnode".
      iDestruct (node_ledger_agree with "HlognX Hlogn") as %->.
      iDestruct (accepted_proposal_lookup with "Hacpt Hpsa") as %Hvnode.
      iDestruct (big_sepM_lookup with "Hpsaubs") as (vub1) "[#Hvub1 %Hprefix1]"; first apply Hvnode.
      iDestruct (proposals_prefix with "Hvub1 Hps") as (vub2) "[%Hvub2 %Hprefix2]".
      assert (Hvsafe : prefix vsafe vub2).
      { trans vnode; first apply Hprefix.
        trans vub1; [apply Hprefix1 | apply Hprefix2].
      }
      iDestruct (big_sepM_lookup with "Hsubsume") as "Hpcmds"; first apply Hvub2.
      rewrite /cpool_subsume_log Forall_forall.
      iIntros (c Hc).
      pose proof (elem_of_prefix _ _ _ Hc Hvsafe) as Hc'.
      iDestruct (big_sepL_elem_of with "Hpcmds") as "Hc"; first apply Hc'.
      iApply (cpool_lookup with "Hc Hcpool").
    }
    iMod (log_update with "Hlogcli Hlog") as "[Hlogcli Hlog]".
    { apply Hext. }
    by iFrame "∗ #".
  Qed.

End commit.
