From Perennial.program_proof.tulip.paxos Require Import prelude.

Section expand.
  Context `{!paxos_ghostG Σ}.

  Lemma node_inv_expand γ nids nid wal terml lsnc logn lsnc' :
    (lsnc ≤ lsnc')%nat ->
    (lsnc' ≤ length logn)%nat ->
    safe_ledger_above γ nids terml (take lsnc' logn) -∗
    own_node_wal_half γ nid wal -∗
    own_committed_lsn_half γ nid lsnc -∗
    own_node_ledger_half γ nid logn -∗
    node_inv γ nids nid terml ==∗
    own_node_wal_half γ nid (wal ++ [CmdPaxosExpand lsnc']) ∗
    own_committed_lsn_half γ nid lsnc' ∗
    own_node_ledger_half γ nid logn ∗
    node_inv γ nids nid terml.
  Proof.
    iIntros (Hge Hle) "#Hcmted HwalX HlsncX HlognX Hinv".
    iNamed "Hinv".
    (* Agreements. *)
    iDestruct (node_wal_agree with "HwalX Hwalnode") as %->.
    iDestruct (committed_lsn_agree with "HlsncX Hlsnc") as %->.
    iDestruct (node_ledger_agree with "HlognX Hlogn") as %->.
    (* Update the write-ahead log. *)
    set wal' := wal ++ _.
    iMod (node_wal_update wal' with "HwalX Hwalnode") as "[HwalX Hwalnode]".
    (* Update the committed LSN. *)
    iMod (committed_lsn_update lsnc' with "HlsncX Hlsnc") as "[HlsncX Hlsnc]".
    iClear "Hsafel".
    iFrame "∗ # %".
    iPureIntro.
    rewrite /execute_paxos_cmds foldl_snoc /= /execute_paxos_expand.
    by rewrite execute_paxos_cmds_unfold Hexec.
  Qed.

  Lemma paxos_inv_expand {γ nids nid wal terml lsnc logn} lsnc' :
    nid ∈ nids ->
    (lsnc ≤ lsnc')%nat ->
    (lsnc' ≤ length logn)%nat ->
    safe_ledger_above γ nids terml (take lsnc' logn) -∗
    own_node_wal_half γ nid wal -∗
    own_ledger_term_half γ nid terml -∗
    own_committed_lsn_half γ nid lsnc -∗
    own_node_ledger_half γ nid logn -∗
    paxos_inv γ nids ==∗
    own_node_wal_half γ nid (wal ++ [CmdPaxosExpand lsnc']) ∗
    own_ledger_term_half γ nid terml ∗
    own_committed_lsn_half γ nid lsnc' ∗
    own_node_ledger_half γ nid logn ∗
    paxos_inv γ nids.
  Proof.
    iIntros (Hnid Hge Hle) "#Hsafel Hwal Hterml Hlsnc Hlogn Hinv".
    iNamed "Hinv".
    rewrite -Hdomtermlm elem_of_dom in Hnid.
    destruct Hnid as [terml' Hnid].
    iDestruct (big_sepM_lookup_acc _ _ nid with "Hnodes") as "[Hnode HnodesC]".
    { apply Hnid. }
    iDestruct (own_ledger_term_node_inv_terml_eq with "Hterml Hnode") as %->.
    (* Re-establish the node invariant. *)
    iMod (node_inv_expand with "Hsafel Hwal Hlsnc Hlogn Hnode") as "(Hwal & Hlsnc & Hlogn & Hnode)".
    { apply Hge. }
    { apply Hle. }
    iDestruct ("HnodesC" with "Hnode") as "Hnodes".
    by iFrame "∗ # %".
  Qed.

End expand.
