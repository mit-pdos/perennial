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
  rewrite lookup_insert_eq in Ht.
  symmetry in Ht. inv Ht.
  destruct Hprev as (termp & Htermp & Htermpc).
  assert (Hlt' : (termp < t')%nat) by lia.
  specialize (Hfree _ _ Htermp _ Ht' Hlt').
  assert (Hne : t' ≠ termc) by lia.
  set_solver.
Qed.

Section ascend.
  Context `{!paxos_ghostG Σ}.

  Lemma node_inv_past_nodedecs_impl_prefix_growing_ledger γ nid ds dslb psa t v :
    dslb !! t = Some (Accept v) ->
    is_past_nodedecs_lb γ nid dslb -∗
    node_inv_ds_psa γ nid ds psa -∗
    prefix_growing_ledger γ t v.
  Proof.
    iIntros (Hv) "Hdslb Hnode".
    iNamed "Hnode". iNamed "Hpsa".
    iDestruct (past_nodedecs_prefix with "Hdslb Hpastd") as %Hprefix.
    pose proof (prefix_lookup_Some _ _ _ _ Hv Hprefix) as Hdst.
    specialize (Hfixed _ _ Hdst).
    by iDestruct (big_sepM_lookup with "Hpsaubs") as "?"; first apply Hfixed.
  Qed.

  Lemma paxos_inv_ascend {γ nids nid wal termc terml lsnc v} ents v' :
    nid ∈ nids ->
    is_term_of_node nid termc ->
    (terml < termc)%nat ->
    (lsnc ≤ length v)%nat ->
    ents = drop lsnc v' ->
    (lsnc ≤ length v')%nat ->
    prefix (take lsnc v) v' ->
    safe_base_proposal_by_length γ nids termc v' -∗
    own_node_wal_half γ nid wal -∗
    own_current_term_half γ nid termc -∗
    own_ledger_term_half γ nid terml -∗
    own_committed_lsn_half γ nid lsnc -∗
    own_node_ledger_half γ nid v -∗
    paxos_inv γ nids ==∗
    own_node_wal_half γ nid (wal ++ [CmdPaxosAdvance termc lsnc ents]) ∗
    own_current_term_half γ nid termc ∗
    own_ledger_term_half γ nid termc ∗
    own_committed_lsn_half γ nid lsnc ∗
    own_node_ledger_half γ nid v' ∗
    paxos_inv γ nids ∗
    own_proposal γ termc v' ∗
    is_base_proposal_receipt γ termc v' ∗
    is_accepted_proposal_lb γ nid termc v'.
  Proof.
    iIntros (Hnid Hton Hlt Hlenv Hents Hlsncub Hlsnc) "#Hsafelen Hwal Htermc Hterml Hlsnc Hv Hinv".
    iNamed "Hinv".
    iAssert (safe_base_proposal γ nids termc v')%nat as "#Hsafe".
    { iNamed "Hsafelen". iNamed "Hvotes".
      rewrite Hdomdss in Hquorum.
      iFrame "Hdss %".
      (* Obtain two nodes [nidx], the node known to have the longest ledger, and
      [nidy], the node to be proved to have the longest ledger. *)
      destruct Hvlatest as (nidx & dsx & Hdsx & Hvx).
      pose proof (longest_proposal_in_term_with_spec (mbind nodedec_to_ledger) dss p) as Hspec.
      destruct (longest_proposal_in_term_with _ _ _) as [vy |] eqn:Hlongest; last first.
      { exfalso.
        specialize (Hspec _ _ Hdsx).
        by rewrite Hvx in Hspec.
      }
      destruct Hspec as [(nidy & dsy & Hdsy & Hvy) Hge].
      rewrite bind_Some in Hvy.
      destruct Hvy as (d & Hvy & Hd).
      apply nodedec_to_ledger_Some_inv in Hd. subst d.
      iAssert (prefix_growing_ledger γ p v')%I as "#Hpfgx".
      { iDestruct (big_sepM_lookup with "Hdss") as "#Hdsx"; first apply Hdsx.
        assert (is_Some (termlm !! nidx)) as [terml' Hterml'].
        { rewrite -elem_of_dom Hdomtermlm.
          apply elem_of_dom_2 in Hdsx.
          destruct Hquorum as [Hincl _].
          set_solver.
        }
        iDestruct (big_sepM_lookup with "Hnodes") as "Hnode"; first apply Hterml'.
        iDestruct (node_inv_extract_ds_psa with "Hnode") as (dss' bs') "[_ Hnode]".
        iApply (node_inv_past_nodedecs_impl_prefix_growing_ledger with "Hdsx Hnode").
        apply Hvx.
      }
      iAssert (prefix_growing_ledger γ p vy)%I as "#Hpfgy".
      { iDestruct (big_sepM_lookup with "Hdss") as "#Hdsy"; first apply Hdsy.
        assert (is_Some (termlm !! nidy)) as [termly Htermly].
        { rewrite -elem_of_dom Hdomtermlm.
          apply elem_of_dom_2 in Hdsy.
          destruct Hquorum as [Hincl _].
          set_solver.
        }
        iDestruct (big_sepM_lookup with "Hnodes") as "Hnode"; first apply Htermly.
        iDestruct (node_inv_extract_ds_psa with "Hnode") as (dssy bsy) "[_ Hnode]".
        iApply (node_inv_past_nodedecs_impl_prefix_growing_ledger with "Hdsy Hnode").
        apply Hvy.
      }
      iDestruct (prefix_growing_ledger_impl_prefix with "Hpfgx Hpfgy") as %Hprefix.
      iPureIntro.
      rewrite /equal_latest_longest_proposal_nodedec /equal_latest_longest_proposal_with.
      case_decide as Htermc; first lia.
      rewrite -latest_term_before_quorum_nodedec_unfold Hlatestq.
      pose proof (length_of_longest_ledger_in_term_spec _ _ _ _ _ Hdsy Hvy) as Hle.
      rewrite Hlongestq in Hle.
      specialize (Hge _ _ Hdsx).
      rewrite Hvx /= in Hge.
      assert (Heqlen : length vy = length v') by lia.
      replace v' with vy; first done.
      by destruct Hprefix as [Hprefix | Hprefix]; rewrite (prefix_length_eq _ _ Hprefix).
    }
    pose proof Hnid as Hterml.
    rewrite -Hdomtermlm elem_of_dom in Hterml.
    destruct Hterml as [terml' Hterml].
    (* Obtain [proposed_cmds γ v']. *)
    iAssert (proposed_cmds γ v')%I as "#Hsubsume'".
    { iNamed "Hsafelen". iNamed "Hvotes".
      destruct Hvlatest as (nidx & dslb & Hdslb & Hv').
      iDestruct (big_sepM_lookup with "Hdss") as "Hdslb"; first apply Hdslb.
      assert (is_Some (termlm !! nidx)) as [termlx Htermlx].
      { destruct Hquorum as [Hquorum _].
        apply elem_of_dom_2 in Hdslb.
        rewrite -elem_of_dom Hdomtermlm.
        set_solver.
      }
      iDestruct (big_sepM_lookup with "Hnodes") as "Hnode"; first apply Htermlx.
      iDestruct (node_inv_extract_ds_psa with "Hnode") as (ds psa) "[_ Hdp]".
      iDestruct (node_inv_past_nodedecs_impl_prefix_growing_ledger with "Hdslb Hdp") as "#Hpfg".
      { apply Hv'. }
      iDestruct "Hpfg" as (vub1) "[Hlb %Hprefix1]".
      iDestruct (proposals_prefix with "Hlb Hps") as %(vub2 & Hvub2 & Hprefix2).
      iDestruct (big_sepM_lookup with "Hsubsume") as "Hsubsume'"; first apply Hvub2.
      assert (prefix v' vub2) as [vapp ->]; first by trans vub1.
      rewrite /proposed_cmds.
      by iDestruct (big_sepL_app with "Hsubsume'") as "[? _]".
    }
    iDestruct (big_sepM_delete _ _ nid with "Hnodes") as "[Hnode Hnodes]".
    { apply Hterml. }
    iDestruct (own_ledger_term_node_inv_terml_eq with "Hterml Hnode") as %->.
    (* Obtain freshness of [termc] before insertion to growing / base proposals. *)
    assert (Hnotin : termc ∉ dom psb).
    { rewrite /free_terms /free_terms_with_partf in Hdompsb.
      destruct Hdompsb as [_ Hfree].
      by specialize (Hfree _ _ Hterml _ Hton Hlt).
    }
    (* Insert [(termc, v')] into the growing proposals and the base proposals. *)
    iMod (proposal_insert termc v' with "Hps") as "[Hps Hp]".
    { apply map_Forall2_dom_L in Hvp as Hdomps. by rewrite Hdomps not_elem_of_dom in Hnotin. }
    iMod (base_proposal_insert termc v' with "Hpsb") as "[Hpsb #Hpsbrcp]".
    { by rewrite not_elem_of_dom in Hnotin. }
    (* Extract witness of the inserted proposal to re-establish the node invariant. *)
    iDestruct (proposal_witness with "Hp") as "#Hplb".
    (* Re-establish node invariant. *)
    iMod (node_inv_advance ents v' with "[] [] Hwal Htermc Hterml Hlsnc Hv Hnode")
      as "(Hwal & Htermc & Hterml & Hlsnc & Hv & Hnode & #Hacptlb)".
    { apply Hlt. }
    { apply Hlenv. }
    { apply Hents. }
    { apply Hlsncub. }
    { apply Hlsnc. }
    { by iFrame "Hpsbrcp". }
    { by iFrame "Hplb". }
    iDestruct (big_sepM_insert_2 with "Hnode Hnodes") as "Hnodes".
    rewrite insert_delete_eq.
    iFrame "∗ # %".
    iModIntro.
    iSplit; first by iApply big_sepM_insert_2.
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
