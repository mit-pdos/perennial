(**
 * Pure/Iris invariant definitions and invariance.
 *)
From Perennial.program_proof.rsm Require Import spaxos_top.

Section pure.
  Context `{Countable A}.

  Definition quorum (c q : gset A) : Prop.
  Admitted.

  Lemma quorums_overlapped c q1 q2 :
    quorum c q1 ->
    quorum c q2 ->
    ∃ x, x ∈ q1 ∧ x ∈ q2.
  Admitted.

  Lemma quorum_not_empty (c q : gset A) :
    quorum c q -> q ≠ empty.
  Proof.
    intros Hquorum.
    destruct (quorums_overlapped _ _ _ Hquorum Hquorum) as (x & Helem & _).
    set_solver.
  Qed.

  Lemma ballots_overlapped (bs bsq1 bsq2 : gmap A ballot) :
    bsq1 ⊆ bs ->
    bsq2 ⊆ bs ->
    quorum (dom bs) (dom bsq1) ->
    quorum (dom bs) (dom bsq2) ->
    ∃ x l, bsq1 !! x = Some l ∧ bsq2 !! x = Some l.
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

  Definition accepted_in (l : ballot) n :=
    l !! n = Some true ∧ n ≠ O.
  
  Definition chosen_in (bs : gmap A ballot) (ps : proposals) n v :=
    ∃ bsq,
      bsq ⊆ bs ∧
      quorum (dom bs) (dom bsq) ∧
      map_Forall (λ _ l, accepted_in l n) bsq ∧
      ps !! n = Some v.

  Definition chosen (bs : gmap A ballot) (ps : proposals) v :=
    ∃ n, chosen_in bs ps n v.

  (* Top-level invariant. *)
  Definition consistency (bs : gmap A ballot) (ps : proposals) :=
    ∀ v1 v2, chosen bs ps v1 -> chosen bs ps v2 -> v1 = v2.

  (* Invariant for [consistency]. *)
  Definition accepted_after_chosen (bs : gmap A ballot) (ps : proposals) :=
    ∀ m n v,
      (m ≤ n)%nat ->
      chosen_in bs ps m v ->
      map_Forall (λ _ l, accepted_in l n -> ps !! n = Some v) bs.

  (* Invariant for [accepted_after_chosen]. *)
  Definition proposed_after_chosen (bs : gmap A ballot) (ps : proposals) :=
    ∀ m n v,
      (m ≤ n)%nat ->
      chosen_in bs ps m v ->
      is_Some (ps !! n) ->
      ps !! n = Some v.

  (* Compute the latest accepted proposal before [n]. *)
  Fixpoint latest_proposal (n : nat) (l : ballot) : nat :=
    match n with
    | O => O
    | S k => match l !! k with
            | Some b => if b : bool (* XXX: why do I need this? *)
                       then k
                       else latest_proposal k l
            | _ => latest_proposal k l
            end
    end.

  Definition largest_proposal_step (x : A) (cur prev : nat) : nat :=
    cur `max` prev.
    (* if (cur <? prev)%nat then prev else cur. *)

  Definition largest_proposal (bsq : gmap A ballot) n :=
    let ps := fmap (latest_proposal n) bsq in
    map_fold largest_proposal_step O ps.

  Definition equal_largest_or_empty (bsq : gmap A ballot) (ps : proposals) n v :=
    largest_proposal bsq n = O ∨
    ps !! (largest_proposal bsq n) = Some v.

  Definition valid_proposal (bs : gmap A ballot) (ps : proposals) n v :=
    ∃ bsq : gmap A ballot,
      bsq ⊆ bs ∧
      quorum (dom bs) (dom bsq) ∧
      map_Forall (λ _ l, (n ≤ length l)%nat) bsq ∧
      equal_largest_or_empty bsq ps n v.

  (* Invariant for [proposed_after_chosen]. *)
  Definition valid_proposals (bs : gmap A ballot) (ps : proposals) :=
    map_Forall (λ n v, valid_proposal bs ps n v) ps.

  (* Invariant for [accepted_after_chosen]; i.e., proposed before accepted. *)
  Definition valid_ballots (bs : gmap A ballot) (ps : proposals) :=
    map_Forall (λ _ l, ∀ n, accepted_in l n -> is_Some (ps !! n)) bs.

  Definition valid_consensus (c : consensus) (bs : gmap A ballot) (ps : proposals) :=
    match c with
    | Chosen v => chosen bs ps v
    | _ => True
    end.
  
  (* Lemmas about [latest_proposal]. *)
  Lemma latest_proposal_le l m :
    (latest_proposal m l ≤ m)%nat.
  Proof.
    induction m as [| m' IHm']; first by simpl.
    simpl.
    destruct (l !! m') as [b |]; last lia.
    destruct b; lia.
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
    destruct (l !! n') as [b |]; last by eauto.
    destruct b; last by eauto.
    etrans; first apply Hle.
    apply latest_proposal_le.
  Qed.

  Lemma latest_proposal_Sn l n :
    accepted_in l n ->
    latest_proposal (S n) l = n.
  Proof.
    intros [Hlookup Hnz].
    simpl.
    by rewrite Hlookup.
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
      destruct b; lia.
    }
    specialize (IHn' Hneq).
    simpl.
    destruct (l !! n') as [b |]; last lia.
    destruct b; lia.
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

  Lemma largest_proposal_ge bs n :
    map_Forall (λ _ l, (latest_proposal n l ≤ largest_proposal bs n)%nat) bs.
  Proof.
    intros x l Hlookup.
    unfold largest_proposal.
    pose proof (largest_proposal_step_ge (latest_proposal n <$> bs)) as Hstep.
    rewrite map_Forall_lookup in Hstep.
    apply (Hstep x (latest_proposal n l)).
    rewrite lookup_fmap.
    by rewrite Hlookup.
  Qed.
  
  Lemma largest_proposal_in bs n :
    bs ≠ ∅ ->
    map_Exists (λ _ l, (latest_proposal n l = largest_proposal bs n)%nat) bs.
  Proof.
    intros Hnonempty.
    unfold largest_proposal.
    pose proof (largest_proposal_step_in (latest_proposal n <$> bs)) as Hstep.
    rewrite fmap_empty_iff in Hstep.
    specialize (Hstep Hnonempty).
    destruct Hstep as (x & m & Hlookup & <-).
    rewrite lookup_fmap fmap_Some in Hlookup.
    destruct Hlookup as (l & Hlookup & Heq).
    by exists x, l.
  Qed.
  
  Lemma largest_proposal_lt bs n :
    n ≠ O ->
    bs ≠ ∅ ->
    (largest_proposal bs n < n)%nat.
  Proof.
    intros Hnz Hnonempty.
    destruct (largest_proposal_in bs n Hnonempty) as (y & ly & _ & <-).
    by apply latest_proposal_lt.
  Qed.

  Lemma largest_proposal_accepted_in bs n1 n2 :
    (n1 < n2)%nat ->
    bs ≠ ∅ ->
    map_Exists (λ _ l, accepted_in l n1) bs ->
    (n1 ≤ largest_proposal bs n2 < n2)%nat ∧ largest_proposal bs n2 ≠ O.
  Proof.
    intros Hn Hnonempty Hacc.
    destruct Hacc as (x & l & Hlookup & Hacc).
    pose proof (largest_proposal_ge bs n2) as Hlargest.
    rewrite map_Forall_lookup in Hlargest.
    specialize (Hlargest _ _ Hlookup).
    pose proof (latest_proposal_accepted_in _ _ _ Hn Hacc).
    split; last first.
    { destruct Hacc as [_ Hnz]. lia. }
    split; first lia.
    destruct (largest_proposal_in bs n2 Hnonempty) as (y & ly & _ & <-).
    apply latest_proposal_lt.
    lia.
  Qed.

  Lemma aac_chosen {bs ps n1 n2 v1 v2} :
    (n1 ≤ n2)%nat ->
    accepted_after_chosen bs ps ->
    chosen_in bs ps n1 v1 ->
    chosen_in bs ps n2 v2 ->
    v1 = v2.
  Proof.
    intros Hle Haac H1 H2.
    unshelve epose proof (Haac n1 n2 v1 _ _) as Haac; [apply Hle | done |].
    destruct H2 as (bsq & Hbsq & Hquorum & Haccq & Hlookupq).
    apply quorum_not_empty in Hquorum.
    rewrite dom_empty_iff_L in Hquorum.
    apply map_choose in Hquorum as (x & l & Hl).
    assert (ps !! n2 = Some v1) as Hlookup.
    { rewrite map_Forall_lookup in Haac.
      apply (Haac x l).
      { eapply lookup_weaken; [apply Hl | apply Hbsq]. }
      rewrite map_Forall_lookup in Haccq.
      by apply (Haccq x l).
    }
    rewrite Hlookupq in Hlookup.
    by inversion Hlookup.
  Qed.

  (* Implication theorems of invariants. *)
  Lemma aac_impl_consistency bs ps :
    accepted_after_chosen bs ps ->
    consistency bs ps.
  Proof.
    intros Hacc.
    intros v1 v2 [n1 Hv1] [n2 Hv2].
    destruct (decide (n1 ≤ n2)%nat) as [Hle | Hgt].
    { eapply (aac_chosen Hle); done. }
    { assert (n2 ≤ n1)%nat as Hle by lia. symmetry. eapply (aac_chosen Hle); done. }
  Qed.

  Lemma valid_proposal_chosen_in bs ps m n u v :
    (m < n)%nat ->
    valid_proposals bs ps ->
    chosen_in bs ps m u ->
    ps !! n = Some v ->
    ∃ k, (ps !! n = ps !! k) ∧ (m ≤ k < n)%nat.
  Proof.
    intros Hmn Hvp Hchosen Hlookup.
    edestruct Hvp as (bsq1 & Hsubseteq1 & Hquorum1 & _ & Heq).
    { apply Hlookup. }
    destruct Hchosen as (bsq2 & Hsubseteq2 & Hquorum2 & Hacc & ?).
    (* Extract intersection between the two quorums. *)
    edestruct ballots_overlapped as (x & l & Hbsq1 & Hbsq2).
    { apply Hsubseteq1. }
    { apply Hsubseteq2. }
    { apply Hquorum1. }
    { apply Hquorum2. }
    rewrite map_Forall_lookup in Hacc.
    specialize (Hacc _ _ Hbsq2).
    destruct (largest_proposal_accepted_in bsq1 m n) as [Hlp Hnz].
    { apply Hmn. }
    { set_solver. }
    { rewrite map_Exists_lookup. by exists x, l. }
    destruct Heq as [Heq | Heq].
    { (* Case: None proposed in the majority. *)
      rewrite Heq in Hnz. congruence.
    }
    { (* Case: Equal the largest proposal. *)
      exists (largest_proposal bsq1 n).
      by rewrite Heq Hlookup.
    }
  Qed.

  Lemma vb_pac_impl_aac bs ps :
    valid_ballots bs ps ->
    proposed_after_chosen bs ps ->
    accepted_after_chosen bs ps.
  Proof.
    intros Hvb Hpac.
    intros m n v Hmn Hchosen x l Hlookup Hacc.
    unfold proposed_after_chosen in Hpac.
    eapply Hpac; [apply Hmn | apply Hchosen |].
    unfold valid_ballots in Hvb.
    rewrite map_Forall_lookup in Hvb.
    eapply Hvb; [apply Hlookup | apply Hacc].
  Qed.

  Lemma vp_impl_pac bs ps :
    valid_proposals bs ps ->
    proposed_after_chosen bs ps.
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

  Theorem vb_vp_impl_consistency {bs ps} :
    valid_ballots bs ps ->
    valid_proposals bs ps ->
    consistency bs ps.
  Proof.
    intros Hvb Hvp.
    apply aac_impl_consistency.
    apply vb_pac_impl_aac; first done.
    by apply vp_impl_pac.
  Qed.

  Definition extend {X : Type} (x : X) (n : nat) (l : list X) :=
    l ++ replicate (n - length l) x.

  Lemma extend_length_ge {X : Type} (x : X) (n : nat) (l : list X) :
    (length l ≤ length (extend x n l))%nat.
  Proof. rewrite app_length. lia. Qed.

  Lemma extend_length {X : Type} (x : X) (n : nat) (l : list X) :
    length (extend x n l) = (n - length l + length l)%nat.
  Proof. rewrite app_length replicate_length. lia. Qed.

  (* Transition functions. *)
  Definition spaxos_accept (bs : gmap A ballot) x n :=
    alter (λ l, extend false n l ++ [true]) x bs.

  Definition spaxos_prepare (bs : gmap A ballot) (x : A) (n : nat) :=
    alter (λ l, extend false n l) x bs.

  Definition spaxos_propose (ps : proposals) (n : nat) (v : string) :=
    <[n := v]> ps.

  (* XXX: this should be general. *)
  Lemma fmap_alter_same
    (m : gmap A ballot) (i : A) (f : ballot -> nat) (g : ballot -> ballot) :
    (∀ x, m !! i = Some x -> f x = f (g x)) ->
    fmap f (alter g i m) = fmap f m.
  Proof.
    intros Hfg.
    apply map_eq.
    intros j.
    do 2 rewrite lookup_fmap.
    destruct (decide (i = j)); last by rewrite lookup_alter_ne.
    subst j.
    rewrite lookup_alter -option_fmap_compose.
    destruct (m !! i) eqn:Hlookup; last by apply fmap_None.
    simpl.
    by rewrite -Hfg.
  Qed.
  
  (* XXX: this should be general. *)
  Lemma map_Forall_alter
    (m : gmap A ballot) (i : A) (P : A -> ballot -> Prop) (f : ballot -> ballot) :
    (∀ x, m !! i = Some x -> P i (f x)) ->
    map_Forall P m ->
    map_Forall P (alter f i m).
  Proof.
    intros Hx HP.
    intros j x Halter.
    destruct (decide (i = j)); last first.
    { rewrite lookup_alter_ne in Halter; last done.
      by apply HP in Halter.
    }
    subst j.
    rewrite lookup_alter in Halter.
    rewrite fmap_Some in Halter.
    destruct Halter as (y & Hlookup & Hy).
    rewrite Hy.
    by apply Hx.
  Qed.

  Lemma latest_proposal_append_eq (n : nat) (l t : ballot) :
    (n ≤ length l)%nat ->
    latest_proposal n (l ++ t) = latest_proposal n l.
  Proof.
    intros Hlen.
    induction n as [| n' IHn']; first done.
    simpl.
    rewrite -IHn'; last by lia.
    rewrite lookup_app_l; [done | lia].
  Qed.

  Lemma largest_proposal_accept_same
    (bs : gmap A ballot) (x : A) (n m : nat) :
    map_Forall (λ _ l, (m ≤ length l)%nat) bs ->
    largest_proposal (spaxos_accept bs x n) m = largest_proposal bs m.
  Proof.
    intros Hlens.
    unfold largest_proposal.
    rewrite fmap_alter_same; first done.
    intros l Hlookup.
    pose proof (map_Forall_lookup_1 _ _ _ _ Hlens Hlookup) as Hlen.
    simpl in Hlen.
    unfold extend.
    rewrite app_assoc_reverse.
    by rewrite latest_proposal_append_eq.
  Qed.

  Lemma largest_proposal_prepare_same
    (bs : gmap A ballot) (x : A) (n m : nat) :
    map_Forall (λ _ l, (m ≤ length l)%nat) bs ->
    largest_proposal (spaxos_prepare bs x n) m = largest_proposal bs m.
  Proof.
    intros Hlens.
    unfold largest_proposal.
    rewrite fmap_alter_same; first done.
    intros l Hlookup.
    pose proof (map_Forall_lookup_1 _ _ _ _ Hlens Hlookup) as Hlen.
    simpl in Hlen.
    unfold extend.
    by rewrite latest_proposal_append_eq.
  Qed.

  Lemma valid_proposal_insert_n bs ps n v1 v2 :
    n ≠ O ->
    valid_proposal bs ps n v1 ->
    valid_proposal bs (<[n := v2]> ps) n v1.
  Proof.
    intros Hnz (bsq & Hsubseteq & Hquorum & Hlen & Heq).
    exists bsq.
    do 3 (split; first done).
    destruct Heq as [Hempty | Heq]; first by left.
    right.
    rewrite -Heq.
    apply lookup_insert_ne.
    pose proof (quorum_not_empty _ _ Hquorum) as Hnonempty.
    rewrite dom_empty_iff_L in Hnonempty.
    pose proof (largest_proposal_lt _ _ Hnz Hnonempty) as Hlt.
    lia.
  Qed.

  Lemma valid_proposal_insert_None bs ps n1 n2 v1 v2 :
    ps !! n1 = None ->
    valid_proposal bs ps n2 v2 ->
    valid_proposal bs (<[n1 := v1]> ps) n2 v2.
  Proof.
    intros Hnone (bsq & Hsubseteq & Hquorum & Hlen & Heq).
    exists bsq.
    do 3 (split; first done).
    destruct Heq as [Hempty | Heq]; first by left.
    right.
    rewrite lookup_insert_ne; first done.
    set_solver.
  Qed.

  Lemma extend_false_accepted_in n1 n2 l :
    accepted_in (extend false n2 l) n1 ->
    accepted_in l n1.
  Proof.
    unfold accepted_in.
    intros [Hlookup Hnz].
    split; last done.
    destruct (decide (n1 < length l)%nat) as [Hlt | Hge].
    { by rewrite lookup_app_l in Hlookup. }
    rewrite lookup_app_r in Hlookup; last lia.
    rewrite lookup_replicate in Hlookup.
    by destruct Hlookup as [Hcontra _].
  Qed.

  (* Invariance w.r.t. to all the transition functions above. *)
  Theorem vp_inv_accept bs ps x n :
    valid_proposals bs ps ->
    valid_proposals (spaxos_accept bs x n) ps.
  Proof.
    intros Hvp.
    intros m v Hdsm.
    apply Hvp in Hdsm as (bsq & Hbsa & Hquorum & Hlens & Heq).
    exists (spaxos_accept bsq x n).
    split; first by apply alter_mono.
    split; first by do 2 rewrite dom_alter_L.
    unfold equal_largest_or_empty.
    split.
    { apply map_Forall_alter; last apply Hlens.
      intros y Hlookup.
      pose proof (map_Forall_lookup_1 _ _ _ _ Hlens Hlookup) as Hlen.
      simpl in Hlen.
      rewrite last_length.
      pose proof (extend_length_ge false n y) as Hextend.
      lia.
    }
    by rewrite largest_proposal_accept_same.
  Qed.

  Theorem vb_inv_accept bs ps x n :
    is_Some (ps !! n) ->
    (∃ l, bs !! x = Some l ∧ length l ≤ n)%nat ->
    valid_ballots bs ps ->
    valid_ballots (spaxos_accept bs x n) ps.
  Proof.
    intros Hpsn Hlen Hvb.
    apply map_Forall_alter; last apply Hvb.
    intros l Hlookup m Hacc.
    unfold valid_ballots in Hvb.
    destruct Hacc as [Hm Hnz].
    destruct (decide (m < length (extend false n l))%nat) as [Hlt | Hge].
    { rewrite lookup_app_l in Hm; last done.
      apply (Hvb x l); first apply Hlookup.
      by eapply extend_false_accepted_in.
    }
    apply not_lt in Hge.
    rewrite lookup_app_r in Hm; last lia.
    rewrite list_lookup_singleton_Some in Hm.
    destruct Hm as [Hle _].
    destruct Hlen as (l' & Hlookup' & Hlen).
    rewrite Hlookup' in Hlookup. inversion Hlookup. subst l'.
    rewrite extend_length in Hge, Hle.
    (* lia solves this using [Hlen, Hge, Hle]. *)
    destruct (decide (n = m)) as [Heq | Hneq]; last lia.
    by rewrite -Heq.
  Qed.

  Theorem vp_inv_prepare bs ps x n :
    valid_proposals bs ps ->
    valid_proposals (spaxos_prepare bs x n) ps.
  Proof.
    intros Hvp.
    intros m v Hdsm.
    apply Hvp in Hdsm as (bsq & Hbsa & Hquorum & Hlens & Heq).
    exists (spaxos_prepare bsq x n).
    split; first by apply alter_mono.
    split; first by do 2 rewrite dom_alter_L.
    unfold equal_largest_or_empty.
    split.
    { apply map_Forall_alter; last apply Hlens.
      intros y Hlookup.
      pose proof (map_Forall_lookup_1 _ _ _ _ Hlens Hlookup) as Hlen.
      simpl in Hlen.
      pose proof (extend_length_ge false n y) as Hextend.
      lia.
    }
    by rewrite largest_proposal_prepare_same.
  Qed.

  Theorem vb_inv_prepare bs ps x n :
    valid_ballots bs ps ->
    valid_ballots (spaxos_prepare bs x n) ps.
  Proof.
    intros Hvb.
    apply map_Forall_alter; last apply Hvb.
    intros l Hlookup m Hacc.
    unfold valid_ballots in Hvb.
    apply (Hvb x l); first apply Hlookup.
    by eapply extend_false_accepted_in.
  Qed.

  Theorem vp_inv_propose {bs ps n v} :
    ps !! n = None ->
    n ≠ O ->
    valid_proposal bs ps n v ->
    valid_proposals bs ps ->
    valid_proposals bs (spaxos_propose ps n v).
  Proof.
    intros Hnone Hnz Hvalid Hvp.
    unfold spaxos_propose.
    apply map_Forall_insert_2; first by apply valid_proposal_insert_n.
    apply (map_Forall_impl _ _ _ Hvp).
    intros n' v' Hmu.
    by apply valid_proposal_insert_None.
  Qed.

  Theorem vb_inv_propose {bs ps} n v :
    valid_ballots bs ps ->
    valid_ballots bs (spaxos_propose ps n v).
  Proof.
    intros Hvb.
    unfold spaxos_propose.
    intros x l Hlookup n' Hacc.
    destruct (decide (n' = n)) as [-> | Hneq]; first by rewrite lookup_insert.
    rewrite lookup_insert_ne; last done.
    by apply (Hvb x l).
  Qed.

  Theorem vc_inv_propose {c bs ps} n v :
    valid_consensus c bs ps ->
    valid_consensus c bs (spaxos_propose ps n v).
  Admitted.

End pure.
