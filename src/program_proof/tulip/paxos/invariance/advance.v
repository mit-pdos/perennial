From Perennial.program_proof.tulip.paxos Require Import prelude.

Lemma free_terms_inv_advance {nid ts tm} termc :
  gt_prev_term tm nid termc ->
  free_terms ts tm ->
  free_terms ts (<[nid := termc]> tm).
Proof.
  intros Hprev [Hdisj Hfree].
  split; first done.
  intros nidx t Ht t' Ht' Hlt.
  destruct (decide (nidx = nid)) as [-> | Hne]; last first.
  { rewrite lookup_insert_ne in Ht; last done.
    by specialize (Hfree _ _ Ht _ Ht' Hlt).
  }
  rewrite lookup_insert_eq in Ht.
  symmetry in Ht. inv Ht.
  destruct Hprev as (termp & Htermp & Htermpc).
  assert (Hlt' : (termp < t')%nat) by lia.
  by specialize (Hfree _ _ Htermp _ Ht' Hlt').
Qed.

Section advance.
  Context `{!paxos_ghostG Σ}.

  Lemma node_inv_advance {γ nids nid wal termc terml lsnc v} ents v' :
    (terml < termc)%nat ->
    (lsnc ≤ length v)%nat ->
    ents = drop lsnc v' ->
    (lsnc ≤ length v')%nat ->
    prefix (take lsnc v) v' ->
    prefix_base_ledger γ termc v' -∗
    prefix_growing_ledger γ termc v' -∗
    own_node_wal_half γ nid wal -∗
    own_current_term_half γ nid termc -∗
    own_ledger_term_half γ nid terml -∗
    own_committed_lsn_half γ nid lsnc -∗
    own_node_ledger_half γ nid v -∗
    node_inv γ nids nid terml ==∗
    own_node_wal_half γ nid (wal ++ [CmdPaxosAdvance termc lsnc ents]) ∗
    own_current_term_half γ nid termc ∗
    own_ledger_term_half γ nid termc ∗
    own_committed_lsn_half γ nid lsnc ∗
    own_node_ledger_half γ nid v' ∗
    node_inv γ nids nid termc ∗
    is_accepted_proposal_lb γ nid termc v'.
  Proof.
    iIntros (Hlt Hlenv Hents Hlsncub Hprefix) "#Hpfb #Hpfg HwalX HtermcX HtermlX HlsncX HlognX Hinv".
    iNamed "Hinv".
    (* Agreements on the current term, committed LSN, and the node ledger. *)
    iDestruct (node_wal_agree with "HwalX Hwalnode") as %->.
    iDestruct (current_term_agree with "HtermcX Htermc") as %->.
    iDestruct (committed_lsn_agree with "HlsncX Hlsnc") as %->.
    iDestruct (node_ledger_agree with "HlognX Hlogn") as %->.
    (* Update the write-ahead log. *)
    set wal' := wal ++ _.
    iMod (node_wal_update wal' with "HwalX Hwalnode") as "[HwalX Hwalnode]".
    (* Update the ledger term to [termc]. *)
    iMod (ledger_term_update termc with "HtermlX Hterml") as "[HtermlX Hterml]".
    (* Update the current ledger to [v']. *)
    iMod (node_ledger_update v' with "HlognX Hlogn") as "[HlognX Hlogn]".
    (* Insert [(termc, v')] into the accepted proposals. *)
    iMod (accepted_proposal_insert termc v' with "Hpsa") as "[Hpsa Hp]".
    { specialize (Hdompsa _ Hlt). by rewrite -not_elem_of_dom. }
    iDestruct (accepted_proposal_witness with "Hp") as "#Hplb".
    (* Re-establish [safe_ledger] w.r.t. [v']. *)
    rewrite -take_idemp (take_prefix_le (take lsnc v) v' _ _ Hprefix); last first.
    { rewrite length_take. clear -Hltlog. lia. }
    iDestruct (safe_ledger_above_mono _ termc with "Hsafel") as "Hsafel'".
    { apply Htermlc. }
    iClear "Hacpt".
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { by iApply big_sepM_insert_2. }
    iSplit.
    { by iApply big_sepM_insert_2. }
    iPureIntro.
    split.
    { (* Re-establish [fixed_proposals]. *)
      intros t d Hd.
      destruct (decide (t = termc)) as [-> | Hne]; last first.
      { rewrite lookup_insert_ne; last done.
        by specialize (Hfixed _ _ Hd).
      }
      exfalso.
      (* Derive contradiction from [Hlends] and [Hd]. *)
      apply lookup_lt_Some in Hd.
      lia.
    }
    split.
    { (* Re-establish [free_terms_after]. *)
      rewrite dom_insert_L.
      intros t Hgttermc.
      assert (Hgtterml : (terml < t)%nat) by lia.
      specialize (Hdompsa _ Hgtterml).
      assert (Hne : t ≠ termc) by lia.
      set_solver.
    }
    split; first done.
    { rewrite /execute_paxos_cmds foldl_snoc /= /execute_paxos_advance.
      rewrite execute_paxos_cmds_unfold Hexec.
      case_decide; last lia.
      f_equal.
      rewrite Hents -{2}(take_drop lsnc v').
      f_equal.
      destruct Hprefix as [l ->].
      rewrite take_app_le; last first.
      { rewrite length_take. clear -Hlenv. lia. }
      by rewrite take_idemp.
    }
  Qed.

  Lemma paxos_inv_advance {γ nids nid wal termc terml lsnc v} ents v' :
    nid ∈ nids ->
    (terml < termc)%nat ->
    (lsnc ≤ length v)%nat ->
    ents = drop lsnc v' ->
    (lsnc ≤ length v')%nat ->
    prefix (take lsnc v) v' ->
    prefix_base_ledger γ termc v' -∗
    prefix_growing_ledger γ termc v' -∗
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
    is_accepted_proposal_lb γ nid termc v'.
  Proof.
    iIntros (Hnid Hlt Hlenv Hents Hlsncub Hprefix) "#Hpfb #Hpfg Hwal Htermc Hterml Hlsnc Hlogn Hinv".
    iNamed "Hinv".
    pose proof Hnid as Hterml.
    rewrite -Hdomtermlm elem_of_dom in Hterml.
    destruct Hterml as [terml' Hterml].
    iDestruct (big_sepM_delete _ _ nid with "Hnodes") as "[Hnode Hnodes]".
    { apply Hterml. }
    iDestruct (own_ledger_term_node_inv_terml_eq with "Hterml Hnode") as %->.
    iMod (node_inv_advance ents v' with "Hpfb Hpfg Hwal Htermc Hterml Hlsnc Hlogn Hnode")
      as "(Hwal & Htermc & Hterml & Hlsnc & Hlogn & Hnode & #Hacptlb)".
    { apply Hlt. }
    { apply Hlenv. }
    { apply Hents. }
    { apply Hlsncub. }
    { apply Hprefix. }
    iDestruct (big_sepM_insert_2 with "Hnode Hnodes") as "Hnodes".
    rewrite insert_delete_eq.
    iFrame "∗ # %".
    iPureIntro.
    split.
    { (* Reestablish that domain of [termlm] equals to [nids]. *)
      rewrite dom_insert_L.
      set_solver.
    }
    { (* Re-establish [free_terms]. *)
      apply free_terms_inv_advance; last done.
      rewrite /gt_prev_term.
      by eauto.
    }
  Qed.

End advance.
