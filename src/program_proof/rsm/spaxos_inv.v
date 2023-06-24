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

  Lemma ledgers_overlapped (ls lsq1 lsq2 : gmap A ledger) :
    lsq1 ⊆ ls ->
    lsq2 ⊆ ls ->
    quorum (dom ls) (dom lsq1) ->
    quorum (dom ls) (dom lsq2) ->
    ∃ x l, lsq1 !! x = Some l ∧ lsq2 !! x = Some l.
  Proof.
    intros Hsubseteq1 Hsubseteq2 Hquorum1 Hquorum2.
    edestruct quorums_overlapped as (x & Hin1 & Hin2).
    { apply Hquorum1. }
    { apply Hquorum2. }
    rewrite elem_of_dom in Hin1.
    rewrite elem_of_dom in Hin2.
    destruct Hin1 as [l1 Hlookup1].
    destruct Hin2 as [l2 Hlookup2].
    pose proof (lookup_weaken _ _ _ _ Hlookup1 Hsubseteq1) as H1.
    pose proof (lookup_weaken _ _ _ _ Hlookup2 Hsubseteq2) as H2.
    exists x, l1.
    split; first done.
    rewrite H1 in H2. by inversion H2.
  Qed.

  Definition accepted_in (l : ledger) n :=
    l !! n = Some n ∧ n ≠ O.
  
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
    cur `max` prev.
    (* if (cur <? prev)%nat then prev else cur. *)

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
  Lemma latest_proposal_le l m :
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
    apply latest_proposal_le.
  Qed.

  Lemma latest_proposal_Sn l n :
    accepted_in l n ->
    latest_proposal (S n) l = n.
  Proof.
    intros [Hlookup Hnz].
    simpl.
    rewrite Hlookup.
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
  
  Lemma latest_proposal_lt l n :
    n ≠ O ->
    (latest_proposal n l < n)%nat.
  Proof.
    induction n as [| n' IHn']; first by simpl.
    intros _.
    destruct (decide (n' = O)) as [-> | Hneq].
    { simpl. destruct (l !! O); last lia.
      case_decide; lia.
    }
    specialize (IHn' Hneq).
    simpl.
    destruct (l !! n') as [n'' |]; last lia.
    case_decide; lia.
  Qed.

  (* Lemmas about [largest_proposal]. TODO: fix the argument order. *)
  Lemma largest_proposal_step_ge ns :
    map_Forall (λ _ n, (n ≤ map_fold largest_proposal_step O ns)%nat) ns.
  Proof.
  Admitted.
  
  Lemma largest_proposal_step_in ns :
    ns ≠ ∅ ->
    map_Exists (λ _ n, (n = map_fold largest_proposal_step O ns)%nat) ns.
  Proof.
  Admitted.

  Lemma largest_proposal_ge ls n :
    map_Forall (λ _ l, (latest_proposal n l ≤ largest_proposal ls n)%nat) ls.
  Proof.
    intros x l Hlookup.
    unfold largest_proposal.
    pose proof (largest_proposal_step_ge (latest_proposal n <$> ls)) as Hstep.
    rewrite map_Forall_lookup in Hstep.
    apply (Hstep x (latest_proposal n l)).
    rewrite lookup_fmap.
    by rewrite Hlookup.
  Qed.
  
  Lemma largest_proposal_in ls n :
    ls ≠ ∅ ->
    map_Exists (λ _ l, (latest_proposal n l = largest_proposal ls n)%nat) ls.
  Proof.
    intros Hnonempty.
    unfold largest_proposal.
    pose proof (largest_proposal_step_in (latest_proposal n <$> ls)) as Hstep.
    rewrite fmap_empty_iff in Hstep.
    specialize (Hstep Hnonempty).
    destruct Hstep as (x & m & Hlookup & <-).
    rewrite lookup_fmap fmap_Some in Hlookup.
    destruct Hlookup as (l & Hlookup & Heq).
    by exists x, l.
  Qed.
  
  Lemma largest_proposal_accepted_in ls n1 n2 :
    (n1 < n2)%nat ->
    ls ≠ ∅ ->
    map_Exists (λ _ l, accepted_in l n1) ls ->
    (n1 ≤ largest_proposal ls n2 < n2)%nat ∧ largest_proposal ls n2 ≠ O.
  Proof.
    intros Hn Hnonempty Hacc.
    destruct Hacc as (x & l & Hlookup & Hacc).
    pose proof (largest_proposal_ge ls n2) as Hlargest.
    rewrite map_Forall_lookup in Hlargest.
    specialize (Hlargest _ _ Hlookup).
    pose proof (latest_proposal_accepted_in _ _ _ Hn Hacc).
    split; last first.
    { destruct Hacc as [_ Hnz]. lia. }
    split; first lia.
    destruct (largest_proposal_in ls n2 Hnonempty) as (y & ly & _ & <-).
    apply latest_proposal_lt.
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

  Lemma valid_proposal_chosen_in ls ds m n u v :
    (m < n)%nat ->
    valid_proposal ls ds ->
    chosen_in ls ds m u ->
    ds !! n = Some v ->
    ∃ k, (ds !! n = ds !! k) ∧ (m ≤ k < n)%nat.
  Proof.
    intros Hmn Hvp Hchosen Hlookup.
    edestruct Hvp as (lsq1 & Hsubseteq1 & Hquorum1 & Heq).
    { apply Hlookup. }
    destruct Hchosen as (lsq2 & Hsubseteq2 & Hquorum2 & Hacc & ?).
    (* Extract intersection between the two quorums. *)
    edestruct ledgers_overlapped as (x & l & Hlsq1 & Hlsq2).
    { apply Hsubseteq1. }
    { apply Hsubseteq2. }
    { apply Hquorum1. }
    { apply Hquorum2. }
    rewrite map_Forall_lookup in Hacc.
    specialize (Hacc _ _ Hlsq2).
    destruct (largest_proposal_accepted_in lsq1 m n) as [Hlp Hnz].
    { apply Hmn. }
    { set_solver. }
    { rewrite map_Exists_lookup. by exists x, l. }
    destruct Heq as [Heq | Heq].
    { (* Case: None proposed in the majority. *)
      rewrite Heq in Hnz. congruence.
    }
    { (* Case: Equal the largest proposal. *)
      exists (largest_proposal lsq1 n).
      by rewrite Heq Hlookup.
    }
  Qed.

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
    destruct (decide (m = n)) as [Heq | Hneq].
    { (* Handle [m = n] as a special case. *)
      rewrite Heq in Hchosen.
      by destruct Hchosen as (_ & _ & _ & _ & Hv).
    }
    assert (Hlt : (m < n)%nat) by lia.
    clear Hmn Hneq.
    edestruct valid_proposal_chosen_in as (k & Heq & Hmkn).
    { apply Hlt. }
    { apply Hvalid. }
    { apply Hchosen. }
    { apply Hlookup. }
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
