From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.invariance Require Import advance.

Lemma free_terms_inv_ascend {nid ts tm} termc :
  gt_prev_term tm nid termc ->
  is_term_of_node nid termc ->
  free_terms ts tm ->
  free_terms ({[termc]} ∪ ts) (<[nid := termc]> tm).
Proof.
  intros Hprev Htermc [Hdisj Hfree].
  split; first done.
  intros nidx t Ht t' Ht' Hlt.
  destruct (decide (nidx = nid)) as [-> | Hne]; last first.
  { destruct (decide (t' = termc)) as [-> | Hne'].
    { by specialize (Hdisj _ _ _ Hne Ht'). }
    rewrite lookup_insert_ne in Ht; last done.
    specialize (Hfree _ _ Ht _ Ht' Hlt).
    set_solver.
  }
  rewrite lookup_insert in Ht.
  symmetry in Ht. inv Ht.
  destruct Hprev as (termp & Htermp & Htermpc).
  assert (Hlt' : (termp < t')%nat) by lia.
  specialize (Hfree _ _ Htermp _ Ht' Hlt').
  assert (Hne : t' ≠ termc) by lia.
  set_solver.
Qed.

Section ascend.
  Context `{!paxos_ghostG Σ}.

  Lemma paxos_inv_ascend γ nids nid termc terml logn logn' :
    nid ∈ nids ->
    is_term_of_node nid termc ->
    (terml < termc)%nat ->
    safe_base_proposal γ nids termc logn' -∗
    own_current_term_half γ nid termc -∗
    own_ledger_term_half γ nid terml -∗
    own_node_ledger_half γ nid logn -∗
    paxos_inv γ nids ==∗
    own_current_term_half γ nid termc ∗
    own_ledger_term_half γ nid termc ∗
    own_node_ledger_half γ nid logn' ∗
    paxos_inv γ nids ∗
    own_proposal γ termc logn' ∗
    is_base_proposal_receipt γ termc logn' ∗
    is_accepted_proposal_lb γ nid termc logn'.
  Proof.
    iIntros (Hnid Hton Hlt) "#Hsafe Htermc Hterml Hlogn Hinv".
    iNamed "Hinv".
    pose proof Hnid as Hterml.
    rewrite -Hdomtermlm elem_of_dom in Hterml.
    destruct Hterml as [terml' Hterml].
    iDestruct (big_sepM_delete _ _ nid with "Hnodes") as "[Hnode Hnodes]".
    { apply Hterml. }
    iDestruct (own_ledger_term_node_inv_terml_eq with "Hterml Hnode") as %->.
    (* Obtain freshness of [termc] before insertion to growing / base proposals. *)
    assert (Hnotin : termc ∉ dom psb).
    { rewrite /free_terms /free_terms_with_partf in Hdompsb.
      destruct Hdompsb as [_ Hfree].
      by specialize (Hfree _ _ Hterml _ Hton Hlt).
    }
    (* Insert [(termc, logn')] into the growing proposals and the base proposals. *)
    iMod (proposal_insert termc logn' with "Hps") as "[Hps Hp]".
    { apply map_Forall2_dom_L in Hvp as Hdomps. by rewrite Hdomps not_elem_of_dom in Hnotin. }
    iMod (base_proposal_insert termc logn' with "Hpsb") as "[Hpsb #Hpsbrcp]".
    { by rewrite not_elem_of_dom in Hnotin. }
    (* Extract witness of the inserted proposal to re-establish the node invariant. *)
    iDestruct (proposal_witness with "Hp") as "#Hplb".
    (* Re-establish node invariant. *)
    iMod (node_inv_advance logn' with "[] [] Htermc Hterml Hlogn Hnode")
      as "(Htermc & Hterml & Hlogn & Hnode & #Hacptlb)".
    { apply Hlt. }
    { by iFrame "Hpsbrcp". }
    { by iFrame "Hplb". }
    iDestruct (big_sepM_insert_2 with "Hnode Hnodes") as "Hnodes".
    rewrite insert_delete_insert.
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { (* Re-establish [safe_base_proposal]. *)
      iApply (big_sepM_insert_2 with "Hsafe Hsafepsb").
    }
    iPureIntro.
    split.
    { (* Re-establish [valid_proposals]. *)
      by apply map_Forall2_insert_2.
    }
    split.
    { (* Reestablish that domain of [termlm] equals to [nids]. *)
      rewrite dom_insert_L.
      set_solver.
    }
    { (* Re-establish [free_terms]. *)
      rewrite dom_insert_L.
      apply free_terms_inv_ascend; [| done | done].
      rewrite /gt_prev_term.
      by eauto.
    }
  Qed.

End ascend.
