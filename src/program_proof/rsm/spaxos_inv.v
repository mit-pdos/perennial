From Perennial.program_proof Require Export grove_prelude.

Section inv.
  Context `{Countable A}.
  
  Definition decrees := gmap nat string.
  Definition ledger := list bool.

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
    l !! n = Some true ∧ n ≠ O.
  
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
            | Some b => if b : bool (* XXX: why do I need this? *)
                       then k
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

  Definition valid_proposal (ls : gmap A ledger) (ds : decrees) n v :=
    ∃ lsq : gmap A ledger,
      lsq ⊆ ls ∧
      quorum (dom ls) (dom lsq) ∧
      map_Forall (λ _ l, (n ≤ length l)%nat) lsq ∧
      equal_largest_or_empty lsq ds n v.

  (* Invariant for [proposed_after_chosen]. *)
  Definition valid_proposals (ls : gmap A ledger) (ds : decrees) :=
    map_Forall (λ n v, valid_proposal ls ds n v) ds.

  (* Invariant for [accepted_after_chosen]; i.e., proposed before accepted. *)
  Definition valid_ledgers (ls : gmap A ledger) (ds : decrees) :=
    map_Forall (λ _ l, ∀ n, accepted_in l n -> is_Some (ds !! n)) ls.
  
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
  
  Lemma largest_proposal_lt ls n :
    n ≠ O ->
    ls ≠ ∅ ->
    (largest_proposal ls n < n)%nat.
  Proof.
    intros Hnz Hnonempty.
    destruct (largest_proposal_in ls n Hnonempty) as (y & ly & _ & <-).
    by apply latest_proposal_lt.
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
  Lemma aac_impl_consistency ls ds :
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
    valid_proposals ls ds ->
    chosen_in ls ds m u ->
    ds !! n = Some v ->
    ∃ k, (ds !! n = ds !! k) ∧ (m ≤ k < n)%nat.
  Proof.
    intros Hmn Hvp Hchosen Hlookup.
    edestruct Hvp as (lsq1 & Hsubseteq1 & Hquorum1 & _ & Heq).
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

  Lemma vl_pac_impl_aac ls ds :
    valid_ledgers ls ds ->
    proposed_after_chosen ls ds ->
    accepted_after_chosen ls ds.
  Proof.
    intros Hvl Hpac.
    intros m n v Hmn Hchosen x l Hlookup Hacc.
    unfold proposed_after_chosen in Hpac.
    eapply Hpac; [apply Hmn | apply Hchosen |].
    unfold valid_ledgers in Hvl.
    rewrite map_Forall_lookup in Hvl.
    eapply Hvl; [apply Hlookup | apply Hacc].
  Qed.

  Lemma vp_impl_pac ls ds :
    valid_proposals ls ds ->
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

  Theorem vp_vl_impl_consistency ls ds :
    valid_proposals ls ds ->
    valid_ledgers ls ds ->
    consistency ls ds.
  Proof.
    intros Hvp Hvl.
    apply aac_impl_consistency.
    apply vl_pac_impl_aac; first done.
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
  Definition accept_trans (ls : gmap A ledger) x n :=
    alter (λ l, extend false n l ++ [true]) x ls.

  Definition prepare_trans (ls : gmap A ledger) (x : A) (n : nat) :=
    alter (λ l, extend false n l) x ls.

  Definition propose_trans (ds : decrees) (n : nat) (v : string) :=
    <[n := v]> ds.

  (* XXX: this should be general. *)
  Lemma fmap_alter_same
    (m : gmap A ledger) (i : A) (f : ledger -> nat) (g : ledger -> ledger) :
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
    (m : gmap A ledger) (i : A) (P : A -> ledger -> Prop) (f : ledger -> ledger) :
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

  Lemma latest_proposal_append_eq (n : nat) (l t : ledger) :
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
    (ls : gmap A ledger) (x : A) (n m : nat) :
    map_Forall (λ _ l, (m ≤ length l)%nat) ls ->
    largest_proposal (accept_trans ls x n) m = largest_proposal ls m.
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
    (ls : gmap A ledger) (x : A) (n m : nat) :
    map_Forall (λ _ l, (m ≤ length l)%nat) ls ->
    largest_proposal (prepare_trans ls x n) m = largest_proposal ls m.
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

  Lemma valid_proposal_insert_n ls ds n v1 v2 :
    n ≠ O ->
    valid_proposal ls ds n v1 ->
    valid_proposal ls (<[n := v2]> ds) n v1.
  Proof.
    intros Hnz (lsq & Hsubseteq & Hquorum & Hlen & Heq).
    exists lsq.
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

  Lemma valid_proposal_insert_None ls ds n1 n2 v1 v2 :
    ds !! n1 = None ->
    valid_proposal ls ds n2 v2 ->
    valid_proposal ls (<[n1 := v1]> ds) n2 v2.
  Proof.
    intros Hnone (lsq & Hsubseteq & Hquorum & Hlen & Heq).
    exists lsq.
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
  Theorem vp_inv_accept ls ls' ds x n :
    ls' = accept_trans ls x n ->
    valid_proposals ls ds ->
    valid_proposals ls' ds.
  Proof.
    intros Htrans Hvp.
    intros m v Hdsm.
    apply Hvp in Hdsm as (lsq & Hlsa & Hquorum & Hlens & Heq).
    exists (accept_trans lsq x n).
    split.
    { rewrite Htrans. by apply alter_mono. }
    split.
    { rewrite Htrans. by do 2 rewrite dom_alter_L. }
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

  Theorem vl_inv_accept ls ls' ds x n :
    is_Some (ds !! n) ->
    (∃ l, ls !! x = Some l ∧ length l ≤ n)%nat ->
    ls' = accept_trans ls x n ->
    valid_ledgers ls ds ->
    valid_ledgers ls' ds.
  Proof.
    intros Hdsn Hlen Htrans Hvl.
    rewrite Htrans.
    apply map_Forall_alter; last apply Hvl.
    intros l Hlookup m Hacc.
    unfold valid_ledgers in Hvl.
    destruct Hacc as [Hm Hnz].
    destruct (decide (m < length (extend false n l))%nat) as [Hlt | Hge].
    { rewrite lookup_app_l in Hm; last done.
      apply (Hvl x l); first apply Hlookup.
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

  Theorem vp_inv_prepare ls ls' ds x n :
    ls' = prepare_trans ls x n ->
    valid_proposals ls ds ->
    valid_proposals ls' ds.
  Proof.
    intros Htrans Hvp.
    intros m v Hdsm.
    apply Hvp in Hdsm as (lsq & Hlsa & Hquorum & Hlens & Heq).
    exists (prepare_trans lsq x n).
    split.
    { rewrite Htrans. by apply alter_mono. }
    split.
    { rewrite Htrans. by do 2 rewrite dom_alter_L. }
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

  Theorem vl_inv_prepare ls ls' ds x n :
    ls' = prepare_trans ls x n ->
    valid_ledgers ls ds ->
    valid_ledgers ls' ds.
  Proof.
    intros Htrans Hvl.
    rewrite Htrans.
    apply map_Forall_alter; last apply Hvl.
    intros l Hlookup m Hacc.
    unfold valid_ledgers in Hvl.
    apply (Hvl x l); first apply Hlookup.
    by eapply extend_false_accepted_in.
  Qed.

  Theorem vp_inv_propose ls ds n v :
    ds !! n = None ->
    n ≠ O ->
    valid_proposal ls ds n v ->
    valid_proposals ls ds ->
    valid_proposals ls (propose_trans ds n v).
  Proof.
    intros Hnone Hnz Hvalid Hvp.
    unfold propose_trans.
    apply map_Forall_insert_2; first by apply valid_proposal_insert_n.
    apply (map_Forall_impl _ _ _ Hvp).
    intros n' v' Hmu.
    by apply valid_proposal_insert_None.
  Qed.

  Theorem vl_inv_propose ls ds n v :
    valid_ledgers ls ds ->
    valid_ledgers ls (propose_trans ds n v).
  Proof.
    intros Hvl.
    unfold propose_trans.
    intros x l Hlookup n' Hacc.
    destruct (decide (n' = n)) as [-> | Hneq]; first by rewrite lookup_insert.
    rewrite lookup_insert_ne; last done.
    by apply (Hvl x l).
  Qed.

End inv.
