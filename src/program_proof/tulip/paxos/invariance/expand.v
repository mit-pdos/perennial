From Perennial.program_proof.tulip.paxos Require Import prelude.

Section expand.
  Context `{!paxos_ghostG Σ}.

  Lemma node_inv_expand γ nids nid terml lsnc logn lsnc' :
    (lsnc ≤ lsnc')%nat ->
    (lsnc' ≤ length logn)%nat ->
    safe_ledger_above γ nids terml (take lsnc' logn) -∗
    own_committed_lsn_half γ nid lsnc -∗
    own_node_ledger_half γ nid logn -∗
    node_inv γ nids nid terml ==∗
    own_committed_lsn_half γ nid lsnc' ∗
    own_node_ledger_half γ nid logn ∗
    node_inv γ nids nid terml.
  Proof.
    iIntros (Hge Hle) "#Hcmted HlsncX HlognX Hinv".
    iNamed "Hinv".
    (* Agreements. *)
    iDestruct (committed_lsn_agree with "HlsncX Hlsnc") as %->.
    iDestruct (node_ledger_agree with "HlognX Hlogn") as %->.
    (* Update the committed LSN. *)
    iMod (committed_lsn_update lsnc' with "HlsncX Hlsnc") as "[HlsncX Hlsnc]".
    iClear "Hsafel".
    by iFrame "∗ # %".
  Qed.

  Lemma paxos_inv_expand {γ nids nid terml lsnc logn} lsnc' :
    nid ∈ nids ->
    (lsnc ≤ lsnc')%nat ->
    (lsnc' ≤ length logn)%nat ->
    safe_ledger_above γ nids terml (take lsnc' logn) -∗
    own_ledger_term_half γ nid terml -∗
    own_committed_lsn_half γ nid lsnc -∗
    own_node_ledger_half γ nid logn -∗
    paxos_inv γ nids ==∗
    own_ledger_term_half γ nid terml ∗
    own_committed_lsn_half γ nid lsnc' ∗
    own_node_ledger_half γ nid logn ∗
    paxos_inv γ nids.
  Proof.
    iIntros (Hnid Hge Hle) "#Hsafel Hterml Hlsnc Hlogn Hinv".
    iNamed "Hinv".
    rewrite -Hdomtermlm elem_of_dom in Hnid.
    destruct Hnid as [terml' Hnid].
    iDestruct (big_sepM_lookup_acc _ _ nid with "Hnodes") as "[Hnode HnodesC]".
    { apply Hnid. }
    iDestruct (own_ledger_term_node_inv_terml_eq with "Hterml Hnode") as %->.
    (* Re-establish the node invariant. *)
    iMod (node_inv_expand with "Hsafel Hlsnc Hlogn Hnode") as "(Hlsnc & Hlogn & Hnode)".
    { apply Hge. }
    { apply Hle. }
    iDestruct ("HnodesC" with "Hnode") as "Hnodes".
    by iFrame "∗ # %".
  Qed.

End expand.
