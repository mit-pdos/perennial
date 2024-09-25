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
