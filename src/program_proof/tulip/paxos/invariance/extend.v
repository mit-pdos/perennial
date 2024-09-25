From Perennial.program_proof.tulip.paxos Require Import prelude.

Section extend.
  Context `{!paxos_ghostG Σ}.

  Lemma paxos_inv_extend γ nids term logn logn' :
    prefix logn logn' ->
    own_proposal γ term logn -∗
    paxos_inv γ nids ==∗
    own_proposal γ term logn' ∗
    paxos_inv γ nids.
  Proof.
    iIntros (Hprefix) "Hp Hinv".
    iNamed "Hinv".
    iDestruct (proposal_lookup with "Hp Hps") as %Hlogn.
    (* Extend the growing proposal to [logn'] and extract a witness. *)
    iMod (proposal_update logn' with "Hp Hps") as "[Hp Hps]"; first apply Hprefix.
    iFrame "∗ # %".
    iPureIntro.
    intros t.
    destruct (decide (t = term)) as [-> | Hne]; last by rewrite lookup_insert_ne.
    rewrite lookup_insert.
    specialize (Hvp term).
    destruct (psb !! term) as [loglb |] eqn:Hloglb; rewrite Hlogn Hloglb /= in Hvp; last done.
    rewrite Hloglb /=.
    by trans logn.
  Qed.

End extend.
