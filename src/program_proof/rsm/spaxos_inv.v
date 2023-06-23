From Perennial.program_proof Require Export grove_prelude.
From Perennial.program_proof.mvcc Require Import mvcc_misc.

Section inv.
  Context `{Countable A}.
  
  Definition ledger := list nat.
  Definition decrees := gmap nat string.

  Definition quorum (c q : gset A) : Prop.
  Admitted.

  Lemma quorum_not_empty (c q : gset A) :
    quorum c q -> q ≠ empty.
  Admitted.

  Lemma quorums_overlapped c q1 q2 :
    quorum c q1 ->
    quorum c q2 ->
    ∃ x, x ∈ q1 ∧ x ∈ q2.
  Admitted.
  
  Definition accepted_in (l : ledger) n :=
    l !! n = Some n.
  
  Definition chosen_in (ls : gmap A ledger) (ds : decrees) n v :=
    ∃ lsq,
      lsq ⊆ ls ∧
      quorum (dom ls) (dom lsq) ∧
      map_Forall (λ _ l, accepted_in l n) lsq ∧
      ds !! n = Some v.

  Definition chosen (ls : gmap A ledger) (ds : decrees) v :=
    ∃ n, chosen_in ls ds n v.

  (* Top-level invariant. *)
  Definition consistency (ls : gmap A ledger) (ds : decrees) :=
    ∀ v1 v2, chosen ls ds v1 -> chosen ls ds v2 -> v1 = v2.

  (* Invariant for [consistency]. *)
  Definition accepted_after_chosen (ls : gmap A ledger) (ds : decrees) :=
    ∀ m n v,
      (m ≤ n)%nat ->
      chosen_in ls ds m v ->
      map_Forall (λ _ l, accepted_in l n -> ds !! n = Some v) ls.

  (* Invariant for [accepted_after_chosen]. *)
  Definition proposed_after_chosen (ls : gmap A ledger) (ds : decrees) :=
    ∀ m n v,
      (m ≤ n)%nat ->
      chosen_in ls ds m v ->
      is_Some (ds !! n) ->
      ds !! n = Some v.
  
  (* Compute the latest accepted proposal before [n]. *)
  Fixpoint latest_proposal (n : nat) (l : ledger) : nat :=
    match n with
    | O => O
    | S k => match l !! k with
            | Some m => if decide (m = k)
                       then m
                       else latest_proposal k l
            | _ => latest_proposal k l
            end
    end.

  Definition largest_proposal_step (x : A) (cur prev : nat) : nat :=
    if (cur <? prev)%nat then prev else cur.

  Definition largest_proposal (lsq : gmap A ledger) n :=
    let ps := fmap (latest_proposal n) lsq in
    map_fold largest_proposal_step O ps.

  Definition equal_largest_or_empty (lsq : gmap A ledger) (ds : decrees) n v :=
    largest_proposal lsq n = O ∨
    ds !! (largest_proposal lsq n) = Some v.
  
  (* Invariant for [accepted_after_chosen]. *)
  Definition valid_proposal (ls : gmap A ledger) (ds : decrees) :=
    ∀ n v,
      ds !! n = Some v ->
      ∃ lsq : gmap A ledger,
        lsq ⊆ ls ∧ quorum (dom ls) (dom lsq) ∧ equal_largest_or_empty lsq ds n v.

  (* Invariant. *)
  Definition accepted_implies_proposed (ls : gmap A ledger) (ds : decrees) :=
    ∀ n, map_Forall (λ _ l, accepted_in l n -> is_Some (ds !! n)) ls.
  
  (* Lemmas about [latest_proposal]. *)
  Lemma latest_proposal_lt l m :
    (latest_proposal m l ≤ m)%nat.
  Proof.
    induction m as [| m' IHm']; first by simpl.
    simpl.
    destruct (l !! m') as [m'' |]; last lia.
    case_decide; lia.
  Qed.

  Lemma latest_proposal_mono l m n :
    (m ≤ n)%nat ->
    (latest_proposal m l ≤ latest_proposal n l)%nat.
  Proof.
    intros Hmn.
    induction n as [| n' IH].
    { assert (Hm : (m = 0)%nat); first lia. by rewrite Hm. }
    destruct (decide (m = S n')); first by rewrite e.
    unshelve epose proof (IH _) as Hle; first lia.
    simpl.
    destruct (l !! n') as [n'' |]; last by eauto.
    case_decide; last by eauto.
    subst n''.
    etrans; first apply Hle.
    apply latest_proposal_lt.
  Qed.

  Lemma latest_proposal_Sn l n :
    accepted_in l n ->
    latest_proposal (S n) l = n.
  Proof.
    intros Hacc.
    simpl.
    unfold accepted_in in Hacc. rewrite Hacc.
    case_decide; done.
  Qed.
  
  Lemma latest_proposal_accepted_in l m n :
    (m < n)%nat ->
    accepted_in l m ->
    (m ≤ latest_proposal n l)%nat.
  Proof.
    intros Hmn Hacc.
    apply latest_proposal_Sn in Hacc.
    rewrite -Hacc.
    apply latest_proposal_mono.
    lia.
  Qed.
    
  Lemma aac_chosen {ls ds n1 n2 v1 v2} :
    (n1 ≤ n2)%nat ->
    accepted_after_chosen ls ds ->
    chosen_in ls ds n1 v1 ->
    chosen_in ls ds n2 v2 ->
    v1 = v2.
  Proof.
    intros Hle Haac H1 H2.
    unshelve epose proof (Haac n1 n2 v1 _ _) as Haac; [apply Hle | done |].
    destruct H2 as (lsq & Hlsq & Hquorum & Haccq & Hlookupq).
    apply quorum_not_empty in Hquorum.
    rewrite dom_empty_iff_L in Hquorum.
    apply map_choose in Hquorum as (x & l & Hl).
    assert (ds !! n2 = Some v1) as Hlookup.
    { rewrite map_Forall_lookup in Haac.
      apply (Haac x l).
      { eapply lookup_weaken; [apply Hl | apply Hlsq]. }
      rewrite map_Forall_lookup in Haccq.
      by apply (Haccq x l).
    }
    rewrite Hlookupq in Hlookup.
    by inversion Hlookup.
  Qed.

  (* Implication theorems of invariants. *)
  Lemma aac_implies_consistency ls ds :
    accepted_after_chosen ls ds ->
    consistency ls ds.
  Proof.
    intros Hacc.
    intros v1 v2 [n1 Hv1] [n2 Hv2].
    destruct (decide (n1 ≤ n2)%nat) as [Hle | Hgt].
    { eapply (aac_chosen Hle); done. }
    { assert (n2 ≤ n1)%nat as Hle by lia. symmetry. eapply (aac_chosen Hle); done. }
  Qed.

  Lemma valid_proposal_chosen_in ls ds m n v :
    (m ≤ n)%nat ->
    valid_proposal ls ds ->
    chosen_in ls ds m v ->
    ∃ k, (ds !! n = ds !! k) ∧ (m ≤ k < n)%nat.
  Proof.
  Admitted.

  Lemma aip_pac_implies_aac ls ds :
    accepted_implies_proposed ls ds ->
    proposed_after_chosen ls ds ->
    accepted_after_chosen ls ds.
  Proof.
    intros Haip Hpac.
    intros m n v Hmn Hchosen x l Hlookup Hacc.
    unfold proposed_after_chosen in Hpac.
    eapply Hpac; [apply Hmn | apply Hchosen |].
    unfold accepted_implies_proposed in Haip.
    specialize (Haip n).
    rewrite map_Forall_lookup in Haip.
    eapply Haip; [apply Hlookup | apply Hacc].
  Qed.
    
  Lemma valid_implies_pac ls ds :
    valid_proposal ls ds ->
    proposed_after_chosen ls ds.
  Proof.
    intros Hvalid.
    intros m n v Hmn Hchosen [v' Hlookup].
    (* https://coq-club.inria.narkive.com/VWS50VZQ/adding-strong-induction-to-the-standard-library *)
    (* strong induction on [n]. *)
    induction (lt_wf n) as [n _ IHn].
    edestruct valid_proposal_chosen_in as (k & Heq & Hmkn).
    { apply Hmn. }
    { apply Hvalid. }
    { apply Hchosen. }
    rewrite Heq.
    rewrite Heq in Hlookup.
    apply IHn; [lia | lia | done].
  Qed.

  Theorem aip_pac_implies_consistency ls ds :
    accepted_implies_proposed ls ds ->
    proposed_after_chosen ls ds ->
    consistency ls ds.
  Proof.
    intros Haip Hpac.
    apply aac_implies_consistency.
    apply aip_pac_implies_aac; done.
  Qed.
    
  (* Transition functions. *)
  Definition accept_trans (ls : gmap A ledger) x n :=
    alter (λ l, (extend n l) ++ [n]) x ls.

  Definition prepare_trans (ls : gmap A ledger) (x : A) (n : nat) :=
    alter (λ l, extend n l) x ls.

  Definition propose_trans (ds : decrees) (n : nat) (v : string) :=
    <[n := v]> ds.

  (* Invariance w.r.t. to all the transition functions above. *)
  Theorem vp_inv_accept ls ls' ds x n :
    ls' = accept_trans ls x n ->
    valid_proposal ls ds ->
    valid_proposal ls' ds.
  Admitted.

  Theorem aip_inv_accept ls ls' ds x n :
    ls' = accept_trans ls x n ->
    accepted_implies_proposed ls ds ->
    accepted_implies_proposed ls' ds.
  Admitted.

  Theorem vp_inv_prepare ls ls' ds x n :
    ls' = prepare_trans ls x n ->
    valid_proposal ls ds ->
    valid_proposal ls' ds.
  Admitted.

  Theorem aip_inv_prepare ls ls' ds x n :
    ls' = prepare_trans ls x n ->
    accepted_implies_proposed ls ds ->
    accepted_implies_proposed ls' ds.
  Admitted.

  Theorem vp_inv_propose ls ds ds' n v :
    ds' = propose_trans ds n v ->
    valid_proposal ls ds ->
    valid_proposal ls ds'.
  Admitted.

  Theorem aip_inv_propose ls ds ds' n v :
    ds' = propose_trans ds n v ->
    accepted_implies_proposed ls ds ->
    accepted_implies_proposed ls ds'.
  Admitted.

End inv.
