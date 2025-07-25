(**
 * Pure invariants and their invariance theorems.
 *)
From Perennial.program_proof.rsm Require Import spaxos_top.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section pure.
  Context `{Countable A}.

  Definition quorum_size (c q : gset A) :=
    size c / 2 < size q.

  Definition quorum (c q : gset A) :=
    q ⊆ c ∧ quorum_size c q.

  Lemma quorums_overlapped c q1 q2 :
    quorum c q1 ->
    quorum c q2 ->
    ∃ x, x ∈ q1 ∧ x ∈ q2.
  Proof.
    intros [Hle1 Hsize1] [Hle2 Hsize2].
    apply dec_stable.
    intros Hcontra.
    assert (Hdisjoint : q1 ## q2) by set_solver.
    apply size_union in Hdisjoint.
    assert (Hsubseteq : q1 ∪ q2 ⊆ c) by set_solver.
    apply subseteq_size in Hsubseteq.
    rewrite Hdisjoint in Hsubseteq.
    clear -Hsize1 Hsize2 Hsubseteq.
    unfold quorum_size in Hsize1, Hsize2.
    lia.
  Qed.

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
    quorum_size (dom bs) (dom bsq1) ->
    quorum_size (dom bs) (dom bsq2) ->
    ∃ x l, bsq1 !! x = Some l ∧ bsq2 !! x = Some l.
  Proof.
    intros Hsubseteq1 Hsubseteq2 Hsize1 Hsize2.
    edestruct quorums_overlapped as (x & Hin1 & Hin2).
    { split; last apply Hsize1. by apply subseteq_dom. }
    { split; last apply Hsize2. by apply subseteq_dom. }
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
    l !! n = Some true.
  
  Definition chosen_in (bs : gmap A ballot) (ps : proposals) n v :=
    ps !! n = Some v ∧
    ∃ bsq,
      bsq ⊆ bs ∧
      quorum_size (dom bs) (dom bsq) ∧
      map_Forall (λ _ l, accepted_in l n) bsq.

  Definition chosen (bs : gmap A ballot) (ps : proposals) v :=
    ∃ n, n ≠ O ∧ chosen_in bs ps n v.

  (* Top-level invariant. *)
  Definition consistency (bs : gmap A ballot) (ps : proposals) :=
    ∀ v1 v2, chosen bs ps v1 -> chosen bs ps v2 -> v1 = v2.

  (* Invariant for [consistency]. *)
  Definition accepted_after_chosen (bs : gmap A ballot) (ps : proposals) :=
    ∀ m n v,
      (O < m < n)%nat ->
      chosen_in bs ps m v ->
      map_Forall (λ _ l, accepted_in l n -> ps !! n = Some v) bs.

  (* Invariant for [accepted_after_chosen]. *)
  Definition proposed_after_chosen (bs : gmap A ballot) (ps : proposals) :=
    ∀ m n v,
      (O < m < n)%nat ->
      chosen_in bs ps m v ->
      is_Some (ps !! n) ->
      ps !! n = Some v.

  (* Compute the latest accepted proposal before [n]. *)
  Fixpoint latest_before (n : nat) (l : ballot) : nat :=
    match n with
    | O => O
    | S k => match l !! k with
            | Some b => if b : bool (* XXX: why do I need this? *)
                       then k
                       else latest_before k l
            | _ => latest_before k l
            end
    end.

  Definition latest_term (l : ballot) := latest_before (length l) l.

  Definition latest_before_quorum_step (x : A) (cur prev : nat) : nat :=
    cur `max` prev.

  Definition latest_before_quorum (n : nat) (bsq : gmap A ballot) :=
    let ps := fmap (latest_before n) bsq in
    map_fold latest_before_quorum_step O ps.

  Definition equal_latest_proposal_or_free (bsq : gmap A ballot) (ps : proposals) n v :=
    latest_before_quorum n bsq = O ∨
    ps !! (latest_before_quorum n bsq) = Some v.

  Definition valid_proposal (bs : gmap A ballot) (ps : proposals) n v :=
    ∃ bsq : gmap A ballot,
      bsq ⊆ bs ∧
      quorum_size (dom bs) (dom bsq) ∧
      map_Forall (λ _ l, (n ≤ length l)%nat) bsq ∧
      equal_latest_proposal_or_free bsq ps n v.

  (* Invariant for [proposed_after_chosen]. *)
  Definition valid_proposals (bs : gmap A ballot) (ps : proposals) :=
    map_Forall (λ n v, valid_proposal bs ps n v) ps.

  (* Invariant for [accepted_after_chosen]; i.e., proposed before accepted. *)
  Definition valid_ballots (bs : gmap A ballot) (ps : proposals) :=
    map_Forall (λ _ l, ∀ n, accepted_in l n -> is_Some (ps !! n)) bs.

  Definition valid_commitment (c : consensus) (bs : gmap A ballot) (ps : proposals) :=
    match c with
    | Chosen v => chosen bs ps v
    | _ => True
    end.

  Definition valid_term (P : A -> nat -> Prop) (ps : proposals) (x : A) (n : nat) :=
    ∀ n', P x n' -> (n < n')%nat -> ps !! n' = None.

  Definition valid_terms (P : A -> nat -> Prop) (ps : proposals) (ts : gmap A nat) :=
    (∀ x1 x2 n, x1 ≠ x2 -> P x1 n -> not (P x2 n)) ∧
    map_Forall (λ x n, valid_term P ps x n) ts.

  (* Definition of and lemmas about [extend]. *)
  Definition extend {X : Type} (x : X) (n : nat) (l : list X) :=
    l ++ replicate (n - length l) x.

  Lemma extend_length_ge {X : Type} (x : X) (n : nat) (l : list X) :
    (length l ≤ length (extend x n l))%nat.
  Proof. rewrite length_app. lia. Qed.

  Lemma extend_length {X : Type} (x : X) (n : nat) (l : list X) :
    length (extend x n l) = (n - length l + length l)%nat.
  Proof. rewrite length_app length_replicate. lia. Qed.

  Lemma extend_prefix {X : Type} (x : X) (n : nat) (l : list X) :
    prefix l (extend x n l).
  Proof. unfold extend. by apply prefix_app_r. Qed.
  
  (* Lemmas about [latest_before]. *)
  Lemma latest_before_le l m :
    (latest_before m l ≤ m)%nat.
  Proof.
    induction m as [| m' IHm']; first by simpl.
    simpl.
    destruct (l !! m') as [b |]; last lia.
    destruct b; lia.
  Qed.

  Lemma latest_before_mono l m n :
    (m ≤ n)%nat ->
    (latest_before m l ≤ latest_before n l)%nat.
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
    apply latest_before_le.
  Qed.

  Lemma latest_before_Sn l n :
    accepted_in l n ->
    latest_before (S n) l = n.
  Proof. intros Haccin. simpl. by rewrite Haccin. Qed.
  
  Lemma latest_before_accepted_in l m n :
    (m < n)%nat ->
    accepted_in l m ->
    (m ≤ latest_before n l)%nat.
  Proof.
    intros Hmn Hacc.
    apply latest_before_Sn in Hacc.
    rewrite -Hacc.
    apply latest_before_mono.
    lia.
  Qed.
  
  Lemma latest_before_lt l n :
    n ≠ O ->
    (latest_before n l < n)%nat.
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

  (* Lemmas about [latest_before_quorum]. *)
  Lemma latest_before_quorum_step_ge ns :
    map_Forall (λ _ n, (n ≤ map_fold latest_before_quorum_step O ns)%nat) ns.
  Proof.
    intros x n.
    apply (map_fold_weak_ind (λ p m, (m !! x = Some n -> n ≤ p)%nat)); first done.
    intros y n' m b _ Hnr Hn'.
    unfold latest_before_quorum_step.
    destruct (decide (y = x)) as [-> | Hne].
    { rewrite lookup_insert_eq in Hn'. inversion_clear Hn'. lia. }
    rewrite lookup_insert_ne in Hn'; [lia | done].
  Qed.

  Lemma latest_before_quorum_step_O_or_exists ns :
    map_fold latest_before_quorum_step O ns = O ∨
    ∃ x, ns !! x = Some (map_fold latest_before_quorum_step O ns).
  Proof.
    apply (map_fold_weak_ind (λ p m, p = O ∨ ∃ x, m !! x = Some p)); first by left.
    intros x n m b Hmx IHm.
    unfold latest_before_quorum_step.
    destruct IHm as [-> | [y Hy]]; right.
    { exists x. rewrite lookup_insert_eq. by rewrite Nat.max_0_r. }
    destruct (decide (b ≤ n)%nat).
    { exists x. rewrite lookup_insert_eq. by replace (_ `max` _)%nat with n by lia. }
    exists y.
    assert (Hne : x ≠ y) by set_solver.
    rewrite lookup_insert_ne; last done. rewrite Hy.
    by replace (_ `max` _)%nat with b by lia.
  Qed.

  Lemma latest_before_quorum_step_in ns :
    ns ≠ ∅ ->
    map_Exists (λ _ n, n = map_fold latest_before_quorum_step O ns) ns.
  Proof.
    intros Hnonempty.
    destruct (latest_before_quorum_step_O_or_exists ns) as [Hz | [x Hx]]; last first.
    { exists x. by eauto. }
    rewrite Hz.
    destruct (decide (O ∈ (map_img ns : gset nat))) as [Hin | Hnotin].
    { rewrite elem_of_map_img in Hin.
      destruct Hin as [x Hx].
      by exists x, O.
    }
    assert (Hallgz : ∀ n, n ∈ (map_img ns : gset nat) -> (0 < n)%nat).
    { intros n Hn. assert (Hnz : n ≠ O) by set_solver. lia. }
    apply map_choose in Hnonempty.
    destruct Hnonempty as (x & n & Hxn).
    apply latest_before_quorum_step_ge in Hxn as Hle.
    rewrite Hz in Hle.
    apply (elem_of_map_img_2 (SA:=gset nat)) in Hxn.
    apply Hallgz in Hxn.
    lia.
  Qed.

  Lemma latest_before_quorum_ge bs n :
    map_Forall (λ _ l, (latest_before n l ≤ latest_before_quorum n bs)%nat) bs.
  Proof.
    intros x l Hlookup.
    unfold latest_before_quorum.
    pose proof (latest_before_quorum_step_ge (latest_before n <$> bs)) as Hstep.
    rewrite map_Forall_lookup in Hstep.
    apply (Hstep x (latest_before n l)).
    rewrite lookup_fmap.
    by rewrite Hlookup.
  Qed.
  
  Lemma latest_before_quorum_in bs n :
    bs ≠ ∅ ->
    map_Exists (λ _ l, (latest_before n l = latest_before_quorum n bs)%nat) bs.
  Proof.
    intros Hnonempty.
    unfold latest_before_quorum.
    pose proof (latest_before_quorum_step_in (latest_before n <$> bs)) as Hstep.
    rewrite fmap_empty_iff in Hstep.
    specialize (Hstep Hnonempty).
    destruct Hstep as (x & m & Hlookup & <-).
    rewrite lookup_fmap fmap_Some in Hlookup.
    destruct Hlookup as (l & Hlookup & Heq).
    by exists x, l.
  Qed.
  
  Lemma latest_before_quorum_lt bs n :
    n ≠ O ->
    bs ≠ ∅ ->
    (latest_before_quorum n bs < n)%nat.
  Proof.
    intros Hnz Hnonempty.
    destruct (latest_before_quorum_in bs n Hnonempty) as (y & ly & _ & <-).
    by apply latest_before_lt.
  Qed.

  Lemma latest_before_quorum_accepted_in bs n1 n2 :
    (n1 < n2)%nat ->
    map_Exists (λ _ l, accepted_in l n1) bs ->
    (n1 ≤ latest_before_quorum n2 bs < n2)%nat.
  Proof.
    intros Hn (x & l & Hlookup & Hacc).
    pose proof (latest_before_quorum_ge bs n2) as Hlargest.
    rewrite map_Forall_lookup in Hlargest.
    specialize (Hlargest _ _ Hlookup).
    pose proof (latest_before_accepted_in _ _ _ Hn Hacc).
    split; first lia.
    assert (Hnonempty : bs ≠ ∅) by set_solver.
    destruct (latest_before_quorum_in bs n2 Hnonempty) as (y & ly & _ & <-).
    apply latest_before_lt.
    lia.
  Qed.

  Lemma latest_before_append_eq (n : nat) (l t : ballot) :
    (n ≤ length l)%nat ->
    latest_before n (l ++ t) = latest_before n l.
  Proof.
    intros Hlen.
    induction n as [| n' IHn']; first done.
    simpl.
    rewrite -IHn'; last by lia.
    rewrite lookup_app_l; [done | lia].
  Qed.

  (* Lemmas about [latest_term]. *)
  Lemma latest_term_snoc_false (l : ballot) :
    latest_term (l ++ [false]) = latest_term l.
  Proof.
    unfold latest_term. rewrite last_length. simpl.
    replace (_ !! length l) with (Some false); last first.
    { symmetry. rewrite lookup_snoc_Some. by right. }
    by apply latest_before_append_eq.
  Qed.

  Lemma latest_term_extend_false (n : nat) (l : ballot) :
    latest_term (extend false n l) = latest_term l.
  Proof.
    unfold extend.
    induction n as [| n' IHn']; first by rewrite app_nil_r.
    destruct (decide (n' < length l)%nat) as [Hlt | Hge].
    { replace (n' - length l)%nat with O in IHn' by lia.
      by replace (S n' - length l)%nat with O by lia.
    }
    replace (S n' - length l)%nat with (S (n' - length l)%nat) by lia.
    by rewrite replicate_S_end assoc latest_term_snoc_false.
  Qed.

  Lemma latest_term_snoc_true (l : ballot) :
    latest_term (l ++ [true]) = length l.
  Proof.
    unfold latest_term. rewrite last_length. simpl.
    rewrite lookup_app_r; last done.
    by replace (_ - _)%nat with O by lia.
  Qed.

  Lemma chosen_in_same_term {bs ps n v1 v2} :
    chosen_in bs ps n v1 ->
    chosen_in bs ps n v2 ->
    v1 = v2.
  Proof. intros [Hv1 _] [Hv2 _]. naive_solver. Qed.

  Lemma aac_chosen {bs ps n1 n2 v1 v2} :
    (O < n1 ≤ n2)%nat ->
    accepted_after_chosen bs ps ->
    chosen_in bs ps n1 v1 ->
    chosen_in bs ps n2 v2 ->
    v1 = v2.
  Proof.
    intros Hle Haac H1 H2.
    destruct (decide (n1 = n2)) as [Heq | Hneq].
    { rewrite Heq in H1. by eapply chosen_in_same_term. }
    assert (Horder : (O < n1 < n2)%nat) by lia.
    unshelve epose proof (Haac n1 n2 v1 _ _) as Haac; [apply Horder | done |].
    destruct H2 as (Hlookupq & bsq & Hbsq & Hsize & Haccq).
    assert (Hquorum : quorum (dom bs) (dom bsq)).
    { split; [by apply subseteq_dom | done]. }
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
    intros v1 v2 [n1 [Hn1 Hv1]] [n2 [Hn2 Hv2]].
    destruct (decide (n1 ≤ n2)%nat) as [Hle | Hgt].
    { assert (Horder : (O < n1 ≤ n2)%nat) by lia. eapply (aac_chosen Horder); done. }
    { assert (Horder : (O < n2 ≤ n1)%nat) by lia. symmetry. eapply (aac_chosen Horder); done. }
  Qed.

  Lemma valid_proposal_chosen_in bs ps m n u v :
    (O < m < n)%nat ->
    valid_proposals bs ps ->
    chosen_in bs ps m u ->
    ps !! n = Some v ->
    ∃ k, (ps !! n = ps !! k) ∧ (m ≤ k < n)%nat.
  Proof.
    intros Hmn Hvp Hchosen Hlookup.
    edestruct Hvp as (bsq1 & Hsubseteq1 & Hquorum1 & _ & Heq).
    { apply Hlookup. }
    destruct Hchosen as (_ & bsq2 & Hsubseteq2 & Hquorum2 & Hacc).
    (* Extract intersection between the two quorums. *)
    edestruct ballots_overlapped as (x & l & Hbsq1 & Hbsq2).
    { apply Hsubseteq1. }
    { apply Hsubseteq2. }
    { apply Hquorum1. }
    { apply Hquorum2. }
    rewrite map_Forall_lookup in Hacc.
    specialize (Hacc _ _ Hbsq2).
    unshelve epose proof (latest_before_quorum_accepted_in bsq1 m n _ _) as Horder.
    { apply Hmn. }
    { rewrite map_Exists_lookup. by exists x, l. }
    destruct Heq as [Heq | Heq].
    { (* Case: None proposed in the majority. *)
      rewrite Heq in Horder. lia.
    }
    { (* Case: Equal the largest proposal. *)
      exists (latest_before_quorum n bsq1).
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
    edestruct valid_proposal_chosen_in as (k & Heq & Hmkn).
    { apply Hmn. }
    { apply Hvalid. }
    { apply Hchosen. }
    { apply Hlookup. }
    rewrite Heq.
    rewrite Heq in Hlookup.
    destruct (decide (m = k)) as [Hmk | Hmk].
    { (* Handle [m = k] as a special case. *)
      rewrite Hmk in Hchosen.
      by destruct Hchosen as [Hpsk _].
    }
    assert (Horder : (m < k < n)%nat) by lia.
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

  Theorem vt_impl_freshness {P : A -> nat -> Prop} {ps ts x n1 n2} :
    ts !! x = Some n1 ->
    (n1 < n2)%nat ->
    P x n2 ->
    valid_terms P ps ts ->
    ps !! n2 = None.
  Proof.
    intros Hts Hn12 Hxn2 [_ Hvt].
    by specialize (Hvt _ _ Hts _ Hxn2 Hn12).
  Qed.

  (* Transition functions. *)
  Definition spaxos_accept (bs : gmap A ballot) x n :=
    alter (λ l, extend false n l ++ [true]) x bs.

  Definition spaxos_prepare (bs : gmap A ballot) (x : A) (n : nat) :=
    alter (λ l, extend false n l) x bs.

  Definition spaxos_propose (ps : proposals) (n : nat) (v : byte_string) :=
    <[n := v]> ps.

  Definition spaxos_advance (ts : gmap A nat) (x : A) (n : nat) :=
    <[x := n]> ts.

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
    rewrite lookup_alter_eq -option_fmap_compose.
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
    rewrite lookup_alter_eq in Halter.
    rewrite fmap_Some in Halter.
    destruct Halter as (y & Hlookup & Hy).
    rewrite Hy.
    by apply Hx.
  Qed.

  Lemma dom_eq_Some_or_None `{Countable A} {B : Type} {m1 m2 : gmap A B} i :
    dom m1 = dom m2 ->
    (is_Some (m1 !! i) ∧ is_Some (m2 !! i)) ∨ (m1 !! i = None ∧ m2 !! i = None).
  Proof.
    intros Hdom.
    rewrite set_eq in Hdom.
    specialize (Hdom i).
    do 2 rewrite elem_of_dom in Hdom.
    destruct (decide (is_Some (m1 !! i))) as [? | Hm1]; first naive_solver.
    destruct (decide (is_Some (m2 !! i))) as [? | Hm2]; first naive_solver.
    rewrite -eq_None_not_Some in Hm1.
    rewrite -eq_None_not_Some in Hm2.
    by right.
  Qed.

  Lemma latest_before_quorum_eq (n : nat) (bs bslb : gmap A ballot) :
    dom bs = dom bslb ->
    map_Forall (λ _ l, (n ≤ length l)%nat) bslb ->
    prefixes bslb bs ->
    latest_before_quorum n bs = latest_before_quorum n bslb.
  Proof.
    intros Hdom Hlen Hprefix.
    unfold latest_before_quorum.
    replace (latest_before n <$> bs) with (latest_before n <$> bslb); first done.
    rewrite map_eq_iff.
    intros x.
    do 2 rewrite lookup_fmap.
    destruct (dom_eq_Some_or_None x Hdom) as [[[l Hl] [lb Hlb]] | [-> ->]]; last done.
    rewrite Hlb Hl.
    simpl.
    f_equal.
    specialize (Hlen _ _ Hlb). simpl in Hlen.
    specialize (Hprefix _ _ _  Hlb Hl).
    destruct Hprefix as [tail ->].
    symmetry.
    by apply latest_before_append_eq.
  Qed.

  Lemma latest_before_quorum_accept_same
    (bs : gmap A ballot) (x : A) (n m : nat) :
    map_Forall (λ _ l, (m ≤ length l)%nat) bs ->
    latest_before_quorum m (spaxos_accept bs x n) = latest_before_quorum m bs.
  Proof.
    intros Hlens.
    unfold latest_before_quorum.
    rewrite fmap_alter_same; first done.
    intros l Hlookup.
    pose proof (map_Forall_lookup_1 _ _ _ _ Hlens Hlookup) as Hlen.
    simpl in Hlen.
    unfold extend.
    rewrite -!assoc.
    by rewrite latest_before_append_eq.
  Qed.

  Lemma latest_before_quorum_prepare_same
    (bs : gmap A ballot) (x : A) (n m : nat) :
    map_Forall (λ _ l, (m ≤ length l)%nat) bs ->
    latest_before_quorum m (spaxos_prepare bs x n) = latest_before_quorum m bs.
  Proof.
    intros Hlens.
    unfold latest_before_quorum.
    rewrite fmap_alter_same; first done.
    intros l Hlookup.
    pose proof (map_Forall_lookup_1 _ _ _ _ Hlens Hlookup) as Hlen.
    simpl in Hlen.
    unfold extend.
    by rewrite latest_before_append_eq.
  Qed.

  Lemma valid_proposal_insert_n bs ps n v :
    n ≠ O ->
    valid_proposal bs ps n v ->
    valid_proposal bs (<[n := v]> ps) n v.
  Proof.
    intros Hnz (bsq & Hsubseteq & Hsize & Hlen & Heq).
    exists bsq.
    do 3 (split; first done).
    destruct Heq as [Hempty | Heq]; first by left.
    right.
    rewrite -Heq.
    apply lookup_insert_ne.
    assert (Hquorum : quorum (dom bs) (dom bsq)).
    { split; [by apply subseteq_dom | done]. }
    pose proof (quorum_not_empty _ _ Hquorum) as Hnonempty.
    rewrite dom_empty_iff_L in Hnonempty.
    pose proof (latest_before_quorum_lt _ _ Hnz Hnonempty) as Hlt.
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
    intros Haccin.
    destruct (decide (n1 < length l)%nat) as [Hlt | Hge].
    { by rewrite lookup_app_l in Haccin. }
    rewrite lookup_app_r in Haccin; last lia.
    rewrite lookup_replicate in Haccin.
    by destruct Haccin as [Hcontra _].
  Qed.

  (* Invariance w.r.t. to all the transition functions above. *)
  Theorem vp_inv_accept {bs ps} x n :
    valid_proposals bs ps ->
    valid_proposals (spaxos_accept bs x n) ps.
  Proof.
    intros Hvp.
    intros m v Hdsm.
    apply Hvp in Hdsm as (bsq & Hbsa & Hquorum & Hlens & Heq).
    exists (spaxos_accept bsq x n).
    split; first by apply alter_mono.
    split; first by do 2 rewrite dom_alter_L.
    unfold equal_latest_proposal_or_free.
    split.
    { apply map_Forall_alter; last apply Hlens.
      intros y Hlookup.
      pose proof (map_Forall_lookup_1 _ _ _ _ Hlens Hlookup) as Hlen.
      simpl in Hlen.
      rewrite last_length.
      pose proof (extend_length_ge false n y) as Hextend.
      lia.
    }
    by rewrite latest_before_quorum_accept_same.
  Qed.

  Theorem vb_inv_accept {bs ps} x n :
    is_Some (ps !! n) ->
    (∃ l, bs !! x = Some l ∧ length l ≤ n)%nat ->
    valid_ballots bs ps ->
    valid_ballots (spaxos_accept bs x n) ps.
  Proof.
    intros Hpsn Hlen Hvb.
    apply map_Forall_alter; last apply Hvb.
    intros l Hlookup m Hm.
    unfold valid_ballots in Hvb.
    destruct (decide (m < length (extend false n l))%nat) as [Hlt | Hge].
    { rewrite /accepted_in lookup_app_l in Hm; last done.
      apply (Hvb x l); first apply Hlookup.
      by eapply extend_false_accepted_in.
    }
    apply not_lt in Hge.
    rewrite /accepted_in lookup_app_r in Hm; last lia.
    rewrite list_lookup_singleton_Some in Hm.
    destruct Hm as [Hle _].
    destruct Hlen as (l' & Hlookup' & Hlen).
    rewrite Hlookup' in Hlookup. inversion Hlookup. subst l'.
    rewrite extend_length in Hge, Hle.
    (* lia solves this using [Hlen, Hge, Hle]. *)
    destruct (decide (n = m)) as [Heq | Hneq]; last lia.
    by rewrite -Heq.
  Qed.

  Theorem vp_inv_prepare {bs ps} x n :
    valid_proposals bs ps ->
    valid_proposals (spaxos_prepare bs x n) ps.
  Proof.
    intros Hvp.
    intros m v Hdsm.
    apply Hvp in Hdsm as (bsq & Hbsa & Hquorum & Hlens & Heq).
    exists (spaxos_prepare bsq x n).
    split; first by apply alter_mono.
    split; first by do 2 rewrite dom_alter_L.
    unfold equal_latest_proposal_or_free.
    split.
    { apply map_Forall_alter; last apply Hlens.
      intros y Hlookup.
      pose proof (map_Forall_lookup_1 _ _ _ _ Hlens Hlookup) as Hlen.
      simpl in Hlen.
      pose proof (extend_length_ge false n y) as Hextend.
      lia.
    }
    by rewrite latest_before_quorum_prepare_same.
  Qed.

  Theorem vb_inv_prepare {bs ps} x n :
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
    destruct (decide (n' = n)) as [-> | Hneq]; first by rewrite lookup_insert_eq.
    rewrite lookup_insert_ne; last done.
    by apply (Hvb x l).
  Qed.

  Theorem vc_inv_propose {c bs ps} n v :
    ps !! n = None ->
    valid_commitment c bs ps ->
    valid_commitment c bs (spaxos_propose ps n v).
  Proof.
    intros Hpsn. unfold valid_commitment.
    destruct c as [v' |]; last done.
    intros [n' (Hnz & Hpsn' & Hbsq)].
    exists n'.
    split; first done.
    split; last by apply Hbsq.
    assert (Hne : n ≠ n') by set_solver.
    rewrite lookup_insert_Some. by right.
  Qed.

  Lemma accepted_in_app_eq b n t :
    accepted_in b n ->
    accepted_in (b ++ t) n.
  Proof. unfold accepted_in. intros Hbn. by apply lookup_app_l_Some. Qed.

  Theorem vc_inv_prepare {c bs ps} x n :
    valid_commitment c bs ps ->
    valid_commitment c (spaxos_prepare bs x n) ps.
  Proof.
    unfold valid_commitment.
    destruct c as [v' |]; last done.
    intros [n' [Hpsn' [Hnz (bsq & Hsubseteq & Hquorum & Haccin)]]].
    exists n'.
    do 2 (split; first done).
    exists (spaxos_prepare bsq x n).
    split; first by apply alter_mono.
    split; first by do 2 rewrite dom_alter_L.
    apply map_Forall_alter; last done.
    intros y Hy.
    specialize (Haccin _ _ Hy).
    by apply accepted_in_app_eq.
  Qed.

  Theorem vc_inv_accept {c bs ps} x n :
    valid_commitment c bs ps ->
    valid_commitment c (spaxos_accept bs x n) ps.
  Proof.
    unfold valid_commitment.
    destruct c as [v' |]; last done.
    intros [n' [Hpsn' [Hnz (bsq & Hsubseteq & Hquorum & Haccin)]]].
    exists n'.
    do 2 (split; first done).
    exists (spaxos_accept bsq x n).
    split; first by apply alter_mono.
    split; first by do 2 rewrite dom_alter_L.
    apply map_Forall_alter; last done.
    intros y Hy.
    specialize (Haccin _ _ Hy).
    rewrite -assoc.
    by apply accepted_in_app_eq.
  Qed.

  Definition gt_prev_term (ts : gmap A nat) (x : A) (n : nat) :=
    (∃ c, ts !! x = Some c ∧ (c < n)%nat).

  Theorem vt_inv_advance {P : A -> nat -> Prop} {ps ts x n} :
    gt_prev_term ts x n ->
    valid_terms P ps ts ->
    valid_terms P ps (spaxos_advance ts x n).
  Proof.
    intros Hprev [Hdisj Hvt].
    split; first done.
    intros y u Hadv u' Hyu' Hlt.
    unfold spaxos_advance in Hadv.
    destruct (decide (y = x)) as [-> | Hne]; last first.
    { rewrite lookup_insert_ne in Hadv; last done.
      by specialize (Hvt _ _ Hadv _ Hyu' Hlt).
    }
    rewrite lookup_insert_eq in Hadv.
    inversion Hadv. subst u. clear Hadv.
    destruct Hprev as (c & Hxc & Hcn).
    assert (Hcu' : (c < u')%nat) by lia.
    by specialize (Hvt _ _ Hxc _ Hyu' Hcu').
  Qed.

  Theorem vt_inv_propose_advance {P : A -> nat -> Prop} {ps ts x n} v :
    gt_prev_term ts x n ->
    P x n ->
    valid_terms P ps ts ->
    valid_terms P (spaxos_propose ps n v) (spaxos_advance ts x n).
  Proof.
    intros Hprev Hxn [Hdisj Hvt].
    split; first done.
    intros y u Hadv u' Hyu' Hlt.
    unfold spaxos_propose.
    unfold spaxos_advance in Hadv.
    destruct (decide (y = x)) as [-> | Hne]; last first.
    { destruct (decide (u' = n)) as [-> | Hne'].
      { by specialize (Hdisj _ _ _ Hne Hyu'). }
      rewrite lookup_insert_ne in Hadv; last done.
      specialize (Hvt _ _ Hadv _ Hyu' Hlt).
      by rewrite lookup_insert_ne.
    }
    rewrite lookup_insert_eq in Hadv.
    inversion Hadv. subst u. clear Hadv.
    rewrite lookup_insert_ne; last lia.
    destruct Hprev as (c & Hxc & Hcn).
    assert (Hcu' : (c < u')%nat) by lia.
    by specialize (Hvt _ _ Hxc _ Hyu' Hcu').
  Qed.

End pure.
