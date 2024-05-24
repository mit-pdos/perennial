(**
 * Pure invariants and their invariance theorems.
 *)
From Perennial.program_proof.rsm Require Import fpaxos_top rsm_misc.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section extend.
  (* Definition of and lemmas about [extend]. *)
  Definition extend {X : Type} (x : X) (n : nat) (l : list X) :=
    l ++ replicate (n - length l) x.

  Lemma extend_length_ge {X : Type} (x : X) (n : nat) (l : list X) :
    (length l ≤ length (extend x n l))%nat.
  Proof. rewrite app_length. lia. Qed.

  Lemma extend_length {X : Type} (x : X) (n : nat) (l : list X) :
    length (extend x n l) = (n - length l + length l)%nat.
  Proof. rewrite app_length replicate_length. lia. Qed.

  Lemma extend_prefix {X : Type} (x : X) (n : nat) (l : list X) :
    prefix l (extend x n l).
  Proof. unfold extend. by apply prefix_app_r. Qed.
End extend.

Section pure.
  Context `{Countable A}.

  Definition cquorum_size (c q : gset A) :=
    size c / 2 < size q.

  Definition cquorum (c q : gset A) :=
    q ⊆ c ∧ cquorum_size c q.

  Definition fquorum_size (c q : gset A) :=
    (* this is more conservative than what Lamport suggests *)
    3 * size c / 4 < size q.

  Definition fquorum (c q : gset A) :=
    q ⊆ c ∧ fquorum_size c q.

  (* Transition functions. *)
  Definition caccept_node n l :=
    extend Reject n l ++ [CAccept].

  Definition caccept (bs : gmap A ballot) x n :=
    alter (λ l, caccept_node n l) x bs.

  Definition faccept_node n v l :=
    extend Reject n l ++ [FAccept v].

  Definition faccept (bs : gmap A ballot) x n v :=
    alter (λ l, faccept_node n v l) x bs.

  Definition prepare_node n l :=
    extend Reject n l.

  Definition prepare (bs : gmap A ballot) x n :=
    alter (λ l,prepare_node n l) x bs.

  Definition propose (ps : proposals) n e :=
    <[n := e]> ps.

  Definition advance (ts : gmap A nat) x n :=
    <[x := n]> ts.

  Lemma quorums_overlapped_raw (c q1 q2 : gset A) :
    q1 ⊆ c ->
    q2 ⊆ c ->
    size c < size q1 + size q2 ->
    ∃ x, x ∈ q1 ∧ x ∈ q2.
  Proof.
    intros Hq1 Hq2 Hsize.
    apply dec_stable.
    intros Hcontra.
    assert (Hdisjoint : q1 ## q2) by set_solver.
    apply size_union in Hdisjoint.
    assert (Hsubseteq : q1 ∪ q2 ⊆ c) by set_solver.
    apply subseteq_size in Hsubseteq.
    rewrite Hdisjoint in Hsubseteq.
    lia.
  Qed.

  Lemma quorums_overlapped c q1 q2 :
    (cquorum c q1 ∨ fquorum c q1) ->
    (cquorum c q2 ∨ fquorum c q2) ->
    ∃ x, x ∈ q1 ∧ x ∈ q2.
  Proof.
    rewrite /cquorum /cquorum_size /fquorum /fquorum_size.
    intros [[Hle1 Hsize1] | [Hle1 Hsize1]] [[Hle2 Hsize2] | [Hle2 Hsize2]];
      (apply (quorums_overlapped_raw c); [done | done | lia]).
  Qed.

  Lemma quorums_sufficient c qc qf :
    cquorum_size c qc ->
    fquorum_size c qf ->
    2 * size c < size qc + 2 * size qf.
  Proof.
    intros Hsizec Hsizef.
    unfold cquorum_size in Hsizec.
    unfold fquorum_size in Hsizef.
    lia.
  Qed.

  Lemma cquorum_not_empty (c q : gset A) :
    cquorum c q -> q ≠ empty.
  Proof.
    intros Hquorum.
    unshelve epose proof (quorums_overlapped c q q _ _) as (x & Helem & _).
    { by left. }
    { by left. }
    set_solver.
  Qed.

  Lemma ballots_overlapped (bs bsq1 bsq2 : gmap A ballot) :
    bsq1 ⊆ bs ->
    bsq2 ⊆ bs ->
    cquorum_size (dom bs) (dom bsq1) ->
    (cquorum_size (dom bs) (dom bsq2) ∨ fquorum_size (dom bs) (dom bsq2)) ->
    ∃ x l, bsq1 !! x = Some l ∧ bsq2 !! x = Some l.
  Proof.
    intros Hsubseteq1 Hsubseteq2 Hsize1 Hsize2.
    unshelve epose proof (quorums_overlapped (dom bs) (dom bsq1) (dom bsq2)) as (x & Hin1 & Hin2).
    { left. split; last apply Hsize1. by apply subseteq_dom. }
    { destruct Hsize2 as [Hsize2 | Hsize2]; [left | right].
      { split; last apply Hsize2. by apply subseteq_dom. }
      { split; last apply Hsize2. by apply subseteq_dom. }
    }
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

  Lemma ballots_not_empty (bs bsq : gmap A ballot) :
    bsq ⊆ bs ->
    cquorum_size (dom bs) (dom bsq) ->
    bsq ≠ ∅.
  Proof.
    intros Hsubseteq Hquorum.
    assert (Hq : cquorum (dom bs) (dom bsq)).
    { split; [by apply subseteq_dom | done]. }
    apply cquorum_not_empty in Hq.
    by rewrite dom_empty_iff_L in Hq.
  Qed.

  Definition accepted_in_classic (l : ballot) n :=
    l !! n = Some CAccept.

  Definition accepted_in_fast (l : ballot) n v :=
    l !! n = Some (FAccept v).

  Definition accepted_in (l : ballot) n :=
    accepted_in_classic l n ∨ ∃ v, accepted_in_fast l n v.

  Definition chosen_in_classic (bs bsq : gmap A ballot) (ps : proposals) n v :=
    ps !! n = Some (Proposed v) ∧
    cquorum_size (dom bs) (dom bsq) ∧
    map_Forall (λ _ l, accepted_in_classic l n) bsq.

  Definition chosen_in_fast (bs bsq : gmap A ballot) (ps : proposals) n v :=
    ps !! n = Some Any ∧
    fquorum_size (dom bs) (dom bsq) ∧
    map_Forall (λ _ l, accepted_in_fast l n v) bsq.

  Definition chosen_in (bs : gmap A ballot) (ps : proposals) n v :=
    ∃ bsq,
      bsq ⊆ bs ∧
      (chosen_in_classic bs bsq ps n v ∨ chosen_in_fast bs bsq ps n v).

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
      ps !! n ≠ Some Any ∧
      map_Forall (λ _ l, accepted_in_classic l n -> ps !! n = Some (Proposed v)) bs.

  (* Invariant for [accepted_after_chosen]. *)
  Definition proposed_after_chosen (bs : gmap A ballot) (ps : proposals) :=
    ∀ m n v,
      (O < m < n)%nat ->
      chosen_in bs ps m v ->
      is_Some (ps !! n) ->
      ps !! n = Some (Proposed v).

  (* Compute the latest accepted proposal before [n]. *)
  Fixpoint latest_before (n : nat) (l : ballot) : nat :=
    match n with
    | O => O
    | S k => match l !! k with
            | Some e => match e with
                       | Reject => latest_before k l
                       | _ => k
                       end
            | _ => latest_before k l
            end
    end.

  Definition latest_term (l : ballot) := latest_before (length l) l.

  Definition latest_before_quorum_step (x : A) (cur prev : nat) : nat :=
    cur `max` prev.

  Definition latest_before_quorum (n : nat) (bsq : gmap A ballot) :=
    let ps := fmap (latest_before n) bsq in
    map_fold latest_before_quorum_step O ps.

  Definition is_fast (l : ballot) (n : nat) (v : string) :=
    l !! n = Some (FAccept v).

  #[local]
  Instance is_fast_decision l n v :
    Decision (is_fast l n v).
  Proof. unfold is_fast. apply _. Qed.

  Definition nfast (bsq : gmap A ballot) (n : nat) (v : string) :=
    size (filter (λ x : A * ballot, is_fast x.2 n v) bsq).

  Definition nfastneg (bsq : gmap A ballot) (n : nat) (v : string) :=
    size (filter (λ x : A * ballot, not (is_fast x.2 n v)) bsq).

  Definition equal_max_occurrence (bsq : gmap A ballot) n v :=
    ∀ v', (nfast bsq n v' ≤ nfast bsq n v)%nat.

  Definition equal_latest_proposal (bsq : gmap A ballot) (ps : proposals) n e :=
    match e with
    | Any => False
    | Proposed v => let k := latest_before_quorum n bsq in
                   match ps !! k with
                   | None => False
                   | Some Any => equal_max_occurrence bsq k v
                   | Some (Proposed v') => v' = v
                   end
    end.

  Definition equal_latest_proposal_or_free (bsq : gmap A ballot) (ps : proposals) n e :=
    latest_before_quorum n bsq = O ∨
    equal_latest_proposal bsq ps n e.

  Definition valid_proposal (bs : gmap A ballot) (ps : proposals) n v :=
    ∃ bsq : gmap A ballot,
      bsq ⊆ bs ∧
      cquorum_size (dom bs) (dom bsq) ∧
      map_Forall (λ _ l, (n ≤ length l)%nat) bsq ∧
      equal_latest_proposal_or_free bsq ps n v.

  (* Invariant for [proposed_after_chosen]. *)
  Definition valid_proposals (bs : gmap A ballot) (ps : proposals) :=
    ps !! O = None (* need this to prove vp_inv_accept *) ∧
    map_Forall (λ n v, valid_proposal bs ps n v) ps.

  (* Invariant for [accepted_after_chosen]; i.e., proposed before accepted. *)
  Definition valid_ballots (bs : gmap A ballot) (ps : proposals) :=
    map_Forall (λ _ l, ∀ n, accepted_in_classic l n -> ∃ v, ps !! n = Some (Proposed v)) bs.

  Definition valid_consensus (c : consensus) (bs : gmap A ballot) (ps : proposals) :=
    match c with
    | Chosen v => chosen bs ps v
    | _ => True
    end.

  Definition valid_term (P : A -> nat -> Prop) (ps : proposals) (x : A) (n : nat) :=
    ∀ n', P x n' -> (n < n')%nat -> ps !! n' = None.

  Definition valid_terms (P : A -> nat -> Prop) (ps : proposals) (ts : gmap A nat) :=
    (∀ x1 x2 n, x1 ≠ x2 -> P x1 n -> not (P x2 n)) ∧
    map_Forall (λ x n, valid_term P ps x n) ts.
  
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
    unshelve epose proof (IH _) as Hle; first lia. simpl.
    destruct (l !! n') as [b |]; last by eauto.
    assert (Hn' : (latest_before m l ≤ n')%nat).
    { etrans; [apply Hle | apply latest_before_le]. }
    by destruct b.
  Qed.

  Lemma latest_before_Sn l n :
    accepted_in l n ->
    latest_before (S n) l = n.
  Proof.
    intros Hacc. simpl.
    by destruct Hacc as [Hacc | [? Hacc]]; rewrite Hacc.
  Qed.
  
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
      destruct v; lia.
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
    apply (map_fold_ind (λ p m, (m !! x = Some n -> n ≤ p)%nat)); first done.
    intros y n' m b _ Hnr Hn'.
    unfold latest_before_quorum_step.
    destruct (decide (y = x)) as [-> | Hne].
    { rewrite lookup_insert in Hn'. inversion_clear Hn'. lia. }
    rewrite lookup_insert_ne in Hn'; [lia | done].
  Qed.

  Lemma latest_before_quorum_step_O_or_exists ns :
    map_fold latest_before_quorum_step O ns = O ∨
    ∃ x, ns !! x = Some (map_fold latest_before_quorum_step O ns).
  Proof.
    apply (map_fold_ind (λ p m, p = O ∨ ∃ x, m !! x = Some p)); first by left.
    intros x n m b Hmx IHm.
    unfold latest_before_quorum_step.
    destruct IHm as [-> | [y Hy]]; right.
    { exists x. rewrite lookup_insert. by rewrite Nat.max_0_r. }
    destruct (decide (b ≤ n)%nat).
    { exists x. rewrite lookup_insert. by replace (_ `max` _)%nat with n by lia. }
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

  Lemma latest_before_quorum_zero bs :
    latest_before_quorum O bs = O.
  Proof.
    destruct (decide (bs = ∅)) as [-> | Hne]; first done.
    by destruct (latest_before_quorum_in _ O Hne) as (_ & l & _ & Hz).
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
  Lemma latest_term_snoc_reject (l : ballot) :
    latest_term (l ++ [Reject]) = latest_term l.
  Proof.
    unfold latest_term. rewrite last_length. simpl.
    replace (_ !! length l) with (Some Reject); last first.
    { symmetry. rewrite lookup_snoc_Some. by right. }
    by apply latest_before_append_eq.
  Qed.

  Lemma latest_term_prepare_node (n : nat) (l : ballot) :
    latest_term (prepare_node n l) = latest_term l.
  Proof.
    rewrite /prepare_node /extend.
    induction n as [| n' IHn']; first by rewrite app_nil_r.
    destruct (decide (n' < length l)%nat) as [Hlt | Hge].
    { replace (n' - length l)%nat with O in IHn' by lia.
      by replace (S n' - length l)%nat with O by lia.
    }
    replace (S n' - length l)%nat with (S (n' - length l)%nat) by lia.
    by rewrite replicate_S_end app_assoc latest_term_snoc_reject.
  Qed.

  Lemma latest_term_snoc_caccept (l : ballot) :
    latest_term (l ++ [CAccept]) = length l.
  Proof.
    unfold latest_term. rewrite last_length. simpl.
    rewrite lookup_app_r; last done.
    by replace (_ - _)%nat with O by lia.
  Qed.

  Lemma chosen_in_same_term {bs ps n v1 v2} :
    chosen_in bs ps n v1 ->
    chosen_in bs ps n v2 ->
    v1 = v2.
  Proof.
    intros (bsq1 & Hbsq1 & Hchosen1) (bsq2 & Hbsq2 & Hchosen2).
    destruct Hchosen1 as [[Hc1 _] | (Hf1 & Hq1 & Hacc1)]; destruct Hchosen2 as [[Hc2 _] | (Hf2 & Hq2 & Hacc2)].
    { naive_solver. }
    { naive_solver. }
    { naive_solver. }
    unshelve epose proof (quorums_overlapped (dom bs) (dom bsq1) (dom bsq2) _ _) as (x & Hx1 & Hx2).
    { right. by split; first apply subseteq_dom. }
    { right. by split; first apply subseteq_dom. }
    apply elem_of_dom in Hx1 as [l1 Hl1].
    apply elem_of_dom in Hx2 as [l2 Hl2].
    specialize (Hacc1 _ _ Hl1). simpl in Hacc1.
    specialize (Hacc2 _ _ Hl2). simpl in Hacc2.
    pose proof (lookup_weaken _ _ _ _ Hl1 Hbsq1) as Hbs1.
    pose proof (lookup_weaken _ _ _ _ Hl2 Hbsq2) as Hbs2.
    rewrite Hbs1 in Hbs2. inversion Hbs2. subst l2.
    unfold accepted_in_fast in Hacc1, Hacc2.
    set_solver.
  Qed.

  Lemma aac_chosen {bs ps n1 n2 v1 v2} :
    (O < n1 ≤ n2)%nat ->
    accepted_after_chosen bs ps ->
    chosen_in bs ps n1 v1 ->
    chosen_in bs ps n2 v2 ->
    v1 = v2.
  Proof.
    intros Hle Haac Hn1 Hn2.
    destruct (decide (n1 = n2)) as [Heq | Hneq].
    { rewrite Heq in Hn1. by eapply chosen_in_same_term. }
    assert (Horder : (O < n1 < n2)%nat) by lia. clear Hle Hneq.
    specialize (Haac _ _ _ Horder Hn1) as [Hnany Haac].
    destruct Hn2 as (bsq & Hbsq & [Hclassic | Hfast]); last first.
    { by destruct Hfast as [? _]. }
    destruct Hclassic as (Hpsn2 & Hsize &Haccq).
    pose proof (ballots_not_empty _ _ Hbsq Hsize) as Hnonempty.
    apply map_choose in Hnonempty as (x & l & Hl).
    assert (Some (Proposed v2) = Some (Proposed v1)) as Hv12.
    { assert (Hxl : bs !! x = Some l).
      { eapply lookup_weaken; [apply Hl | apply Hbsq]. }
      specialize (Haccq _ _ Hl). simpl in Haccq.
      specialize (Haac _ _ Hxl Haccq).
      by rewrite Hpsn2 in Haac.
    }
    by inversion Hv12.
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

  Lemma vb_pac_impl_aac bs ps :
    valid_ballots bs ps ->
    proposed_after_chosen bs ps ->
    accepted_after_chosen bs ps.
  Proof.
    intros Hvb Hpac.
    intros m n v Hmn Hchosen.
    split.
    { intros Hpsn.
      specialize (Hpac _ _ _ Hmn Hchosen).
      set_solver.
    }
    intros x l Hlookup Hacc.
    unfold proposed_after_chosen in Hpac.
    eapply Hpac; [apply Hmn | apply Hchosen |].
    unfold valid_ballots in Hvb.
    specialize (Hvb _ _ Hlookup _ Hacc).
    set_solver.
  Qed.

  Lemma nfast_nfastneg_dom_size bs n v :
    (nfast bs n v + nfastneg bs n v)%nat = size (dom bs).
  Proof.
    rewrite size_dom -map_size_disj_union.
    { by rewrite map_filter_union_complement. }
    apply map_disjoint_filter_complement.
  Qed.

  (**
   * Informally, this lemma says that if [v] is chosen by some fast quorum,
   * then [v] reaches majority in *any* classic quorum.
   *)
  Lemma cfquorums_nfast {bs bsqc bsqf n v} :
    bsqc ⊆ bs ->
    cquorum_size (dom bs) (dom bsqc) ->
    bsqf ⊆ bs ->
    fquorum_size (dom bs) (dom bsqf) ->
    map_Forall (λ _ l, accepted_in_fast l n v) bsqf ->
    ∀ v', v' ≠ v -> (nfast bsqc n v' < nfast bsqc n v)%nat.
  Proof.
    intros Hbsqc Hqc Hbsqf Hqf Hacc v' Hne.
    apply dec_stable. intros Hle. rewrite Nat.nlt_ge in Hle.
    assert (Hsizef : (size (dom bsqf) = nfast bsqf n v)%nat).
    { clear -Hacc.
      rewrite /nfast size_dom map_filter_id; first done.
      intros x l Hxl.
      by specialize (Hacc _ _ Hxl).
    }
    assert (Hf : (nfast bsqf n v ≤ nfast bs n v)%nat).
    { by apply map_subseteq_size, map_filter_subseteq_mono. }
    assert (Hsizec : ((size (dom bsqc) ≤ 2 * nfastneg bsqc n v)%nat)).
    { pose proof (nfast_nfastneg_dom_size bsqc n v) as Hsizedom.
      assert (Hv' : (nfast bsqc n v' ≤ nfastneg bsqc n v)%nat).
      { clear -Hne Hle.
        rewrite /nfast /nfastneg /is_fast.
        apply map_subseteq_size.
        rewrite map_filter_subseteq_ext.
        naive_solver.
      }
      lia.
    }
    assert (Hc : (nfastneg bsqc n v ≤ nfastneg bs n v)%nat).
    { by apply map_subseteq_size, map_filter_subseteq_mono. }
    pose proof (nfast_nfastneg_dom_size bs n v) as Hsize.
    epose proof (quorums_sufficient _ _ _ Hqc Hqf) as Hsuff.
    lia.
  Qed.

  Lemma vp_impl_pac bs ps :
    valid_proposals bs ps ->
    proposed_after_chosen bs ps.
  Proof.
    intros [_ Hvp].
    intros m n v Hmn Hchosen Hpsn.
    (* https://coq-club.inria.narkive.com/VWS50VZQ/adding-strong-induction-to-the-standard-library *)
    (* strong induction on [n]. *)
    induction (lt_wf n) as [n _ IHn].
    destruct Hpsn as [e Hlookup].
    edestruct Hvp as (bsq1 & Hsubseteq1 & Hquorum1 & _ & Heq).
    { apply Hlookup. }
    destruct Hchosen as (bsq2 & Hsubseteq2 & Hchosen).
    edestruct ballots_overlapped as (x & l & Hbsq1 & Hbsq2).
    { apply Hsubseteq1. }
    { apply Hsubseteq2. }
    { apply Hquorum1. }
    { destruct Hchosen as [(_ & ? & _) | (_ & ? & _)]; [by left | by right]. }
    unshelve epose proof (latest_before_quorum_accepted_in bsq1 m n _ _) as Horder.
    { apply Hmn. }
    { rewrite map_Exists_lookup.
      destruct Hchosen as [(_ & _ & Hacc) | (_ & _ & Hacc)]; specialize (Hacc _ _ Hbsq2); exists x, l.
      { by split; [ | left]. }
      { split; first done. right. simpl in Hacc. by eauto. }
    }
    destruct Heq as [Heq | Heq].
    { exfalso. rewrite Heq in Horder. lia. }
    unfold equal_latest_proposal in Heq.
    set k := latest_before_quorum _ _ in Horder Heq.
    destruct (decide (m = k)) as [Hmk | Hmk]; last first.
    { (* Case: [m < k < n]. *)
      assert (Hmkn : (m < k < n)%nat) by lia. clear Horder Hmk.
      destruct e as [| u]; first done. simpl in Heq.
      destruct (ps !! k) as [u' |] eqn:Hpsk; last done.
      unshelve epose proof (IHn k _ _ _) as Hv; [lia | lia | done |].
      rewrite Hv in Hpsk. inversion Hpsk. subst u'.
      by rewrite Heq.
    }
    { (* Case: [m = k]. *)
      destruct e as [| u]; first done.
      destruct (ps !! k) as [u' |] eqn:Hpsk; last done.
      destruct Hchosen as [(Hpsm & _ & _) | (Hpsm & Hquorum2 & Hacc)];
        subst m; rewrite Hpsm in Hpsk; inversion Hpsk; subst u'.
      { (* Case: [k] is a classic round. *)
        by rewrite Heq.
      }
      { (* Case: [k] is a fast round. Core reasoning in fpaxos. *)
        rewrite Hlookup.
        clear -Hsubseteq1 Hsubseteq2 Hquorum1 Hquorum2 Hacc Heq.
        unfold equal_max_occurrence in Heq.
        pose proof (cfquorums_nfast Hsubseteq1 Hquorum1 Hsubseteq2 Hquorum2 Hacc) as Hv.
        destruct (decide (u = v)) as [-> | Hneq]; first done.
        specialize (Heq v). specialize (Hv u). lia.
      }
    }
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

  Lemma latest_before_quorum_caccept (bs : gmap A ballot) x n1 n2 :
    map_Forall (λ _ l, (n2 ≤ length l)%nat) bs ->
    latest_before_quorum n2 (caccept bs x n1) = latest_before_quorum n2 bs.
  Proof.
    intros Hlens.
    rewrite /latest_before_quorum fmap_alter_same; first done.
    intros l Hlookup.
    pose proof (map_Forall_lookup_1 _ _ _ _ Hlens Hlookup) as Hlen. simpl in Hlen.
    by rewrite /extend /caccept_node -app_assoc latest_before_append_eq.
  Qed.

  Lemma latest_before_quorum_faccept (bs : gmap A ballot) x n1 n2 v :
    map_Forall (λ _ l, (n2 ≤ length l)%nat) bs ->
    latest_before_quorum n2 (faccept bs x n1 v) = latest_before_quorum n2 bs.
  Proof.
    intros Hlens.
    rewrite /latest_before_quorum fmap_alter_same; first done.
    intros l Hlookup.
    pose proof (map_Forall_lookup_1 _ _ _ _ Hlens Hlookup) as Hlen. simpl in Hlen.
    by rewrite /extend /faccept_node -app_assoc latest_before_append_eq.
  Qed.

  Lemma latest_before_quorum_prepare (bs : gmap A ballot) x n1 n2 :
    map_Forall (λ _ l, (n2 ≤ length l)%nat) bs ->
    latest_before_quorum n2 (prepare bs x n1) = latest_before_quorum n2 bs.
  Proof.
    intros Hlens.
    rewrite /latest_before_quorum fmap_alter_same; first done.
    intros l Hlookup.
    pose proof (map_Forall_lookup_1 _ _ _ _ Hlens Hlookup) as Hlen. simpl in Hlen.
    by rewrite latest_before_append_eq.
  Qed.

  Lemma is_fast_prefix_iff l1 l2 n v :
    prefix l1 l2 ->
    (n < length l1)%nat ->
    is_fast l2 n v ↔ is_fast l1 n v.
  Proof.
    intros [t Hprefix] Hlen. rewrite /is_fast Hprefix. split; intros Hl.
    { rewrite lookup_app_Some in Hl. destruct Hl; [done | lia]. }
    { rewrite lookup_app_Some. by left. }
  Qed.

  Lemma nfast_alter_prefix (bs : gmap A ballot) x n v f :
    (∀ l, prefix l (f l)) ->
    map_Forall (λ _ l, (n < length l)%nat) bs ->
    nfast (alter f x bs) n v = nfast bs n v.
  Proof.
    intros Hf Hlen.
    destruct (bs !! x) as [l |] eqn:Hbsx; last by rewrite lookup_alter_None.
    erewrite lookup_alter_Some; last apply Hbsx.
    rewrite /nfast map_filter_insert.
    specialize (Hlen _ _ Hbsx). simpl in Hlen.
    case_decide as Hfast; simpl in Hfast.
    { rewrite map_size_insert_Some; first done.
      rewrite (is_fast_prefix_iff l) in Hfast; [| done | done].
      exists l. by apply map_lookup_filter_Some_2.
    }
    { rewrite map_filter_delete_not; first done.
      intros l' Hbsx' Hfast'. simpl in Hfast'.
      assert (l' = l) as -> by set_solver.
      by rewrite (is_fast_prefix_iff l) in Hfast.
    }
  Qed.

  Lemma nfast_caccept (bs : gmap A ballot) x n1 n2 v :
    map_Forall (λ _ l, (n2 < length l)%nat) bs ->
    nfast (caccept bs x n1) n2 v = nfast bs n2 v.
  Proof.
    intros Hlen.
    apply nfast_alter_prefix; last done.
    intros l.
    rewrite /caccept_node /extend.
    by do 2 apply prefix_app_r.
  Qed.

  Lemma nfast_faccept (bs : gmap A ballot) x n1 n2 v1 v2 :
    map_Forall (λ _ l, (n2 < length l)%nat) bs ->
    nfast (faccept bs x n1 v1) n2 v2 = nfast bs n2 v2.
  Proof.
    intros Hlen.
    apply nfast_alter_prefix; last done.
    intros l.
    rewrite /caccept_node /extend.
    by do 2 apply prefix_app_r.
  Qed.

  Lemma nfast_prepare (bs : gmap A ballot) x n1 n2 v :
    map_Forall (λ _ l, (n2 < length l)%nat) bs ->
    nfast (prepare bs x n1) n2 v = nfast bs n2 v.
  Proof.
    intros Hlen.
    apply nfast_alter_prefix; last done.
    intros l.
    rewrite /caccept_node /extend.
    by apply prefix_app_r.
  Qed.

  Lemma equal_max_occurrence_caccept_iff (bs : gmap A ballot) x n1 n2 v :
    map_Forall (λ _ l, (n2 < length l)%nat) bs ->
    equal_max_occurrence (caccept bs x n1) n2 v ↔
    equal_max_occurrence bs n2 v.
  Proof.
    intros Hlen. unfold equal_max_occurrence.
    split.
    - intros Hmax v'. by do 2 (rewrite -(nfast_caccept bs x n1); last done).
    - intros Hmax v'. by do 2 (rewrite nfast_caccept; last done).
  Qed.

  Lemma equal_max_occurrence_faccept_iff (bs : gmap A ballot) x n1 n2 v1 v2 :
    map_Forall (λ _ l, (n2 < length l)%nat) bs ->
    equal_max_occurrence (faccept bs x n1 v1) n2 v2 ↔
    equal_max_occurrence bs n2 v2.
  Proof.
    intros Hlen. unfold equal_max_occurrence.
    split.
    - intros Hmax v'. by do 2 (rewrite -(nfast_faccept bs x n1 n2 v1); last done).
    - intros Hmax v'. by do 2 (rewrite nfast_faccept; last done).
  Qed.

  Lemma equal_max_occurrence_prepare_iff (bs : gmap A ballot) x n1 n2 v :
    map_Forall (λ _ l, (n2 < length l)%nat) bs ->
    equal_max_occurrence (prepare bs x n1) n2 v ↔
    equal_max_occurrence bs n2 v.
  Proof.
    intros Hlen. unfold equal_max_occurrence.
    split.
    - intros Hmax v'. by do 2 (rewrite -(nfast_prepare bs x n1); last done).
    - intros Hmax v'. by do 2 (rewrite nfast_prepare; last done).
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
    unfold equal_latest_proposal.
    set k := latest_before_quorum n bsq.
    replace (<[n := v]> ps !! k) with (ps !! k); first done.
    symmetry. apply lookup_insert_ne.
    pose proof (ballots_not_empty _ _ Hsubseteq Hsize) as Hnonempty.
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
    move: Heq. unfold equal_latest_proposal.
    set k := latest_before_quorum n2 bsq. intros Heq.
    replace (<[n1 := v1]> ps !! k) with (ps !! k); first done.
    rewrite lookup_insert_ne; first done.
    destruct v2; first done. destruct (ps !! k) eqn:Hpsk; last done.
    set_solver.
  Qed.

  Lemma prepare_node_accepted_in_classic n1 n2 l :
    accepted_in_classic (prepare_node n2 l) n1 ->
    accepted_in_classic l n1.
  Proof.
    unfold accepted_in_classic.
    intros Haccin.
    destruct (decide (n1 < length l)%nat) as [Hlt | Hge].
    { by rewrite lookup_app_l in Haccin. }
    rewrite lookup_app_r in Haccin; last lia.
    rewrite lookup_replicate in Haccin.
    by destruct Haccin as [Hcontra _].
  Qed.

  Lemma faccept_node_accepted_in_classic n1 n2 l v :
    accepted_in_classic (faccept_node n2 v l) n1 ->
    accepted_in_classic l n1.
  Proof.
    rewrite /accepted_in_classic /faccept_node /extend -app_assoc.
    intros Haccin.
    destruct (decide (n1 < length l)%nat) as [Hlt | Hge].
    { by rewrite lookup_app_l in Haccin. }
    rewrite lookup_app_r in Haccin; last lia.
    rewrite lookup_snoc_Some in Haccin.
    destruct Haccin as [[_ Hlookup] | [_ ?]]; last done.
    rewrite lookup_replicate in Hlookup.
    by destruct Hlookup as [Hcontra _].
  Qed.

  (**
   * Invariance of [valid_proposals].
   *)
  Theorem vp_inv_prepare {bs ps} x n :
    valid_proposals bs ps ->
    valid_proposals (prepare bs x n) ps.
  Proof.
    intros [Hpsz Hvp]. split; first done.
    intros m e Hdsm.
    apply Hvp in Hdsm as (bsq & Hbsq & Hquorum & Hlens & Heq).
    exists (prepare bsq x n).
    split; first by apply alter_mono.
    split; first by do 2 rewrite dom_alter_L.
    unfold equal_latest_proposal_or_free.
    split.
    { apply map_Forall_alter; last apply Hlens.
      intros y Hlookup.
      pose proof (map_Forall_lookup_1 _ _ _ _ Hlens Hlookup) as Hlen.
      simpl in Hlen.
      pose proof (extend_length_ge Reject n y) as Hextend.
      unfold prepare_node.
      lia.
    }
    unfold equal_latest_proposal.
    rewrite latest_before_quorum_prepare; last done.
    destruct Heq as [? | Heq]; [by left | right].
    destruct e as [| v]; first done. simpl in Heq.
    destruct (ps !! latest_before_quorum _ _) as [psl |] eqn:Hpsk; last done.
    destruct psl; last done.
    rewrite equal_max_occurrence_prepare_iff; first done.
    apply (map_Forall_impl _ _ _ Hlens). intros _ l Hl.
    eapply Nat.lt_le_trans; last apply Hl.
    apply latest_before_quorum_lt.
    { intros Hz. by rewrite Hz latest_before_quorum_zero Hpsz in Hpsk. }
    by apply (ballots_not_empty bs).
  Qed.

  Theorem vp_inv_propose {bs ps n e} :
    ps !! n = None ->
    n ≠ O ->
    valid_proposal bs ps n e ->
    valid_proposals bs ps ->
    valid_proposals bs (propose ps n e).
  Proof.
    intros Hnone Hnz Hvalid [Hpsz Hvp].
    unfold propose.
    split; first by rewrite lookup_insert_None.
    apply map_Forall_insert_2; first by apply valid_proposal_insert_n.
    apply (map_Forall_impl _ _ _ Hvp).
    intros n' e' Hmu.
    by apply valid_proposal_insert_None.
  Qed.

  Theorem vp_inv_caccept {bs ps} x n :
    valid_proposals bs ps ->
    valid_proposals (caccept bs x n) ps.
  Proof.
    intros [Hpsz Hvp].
    split; first done. intros m e Hdsm.
    apply Hvp in Hdsm as (bsq & Hbsq & Hquorum & Hlens & Heq).
    exists (caccept bsq x n).
    split; first by apply alter_mono.
    split; first by do 2 rewrite dom_alter_L.
    unfold equal_latest_proposal_or_free.
    split.
    { apply map_Forall_alter; last apply Hlens.
      intros y Hlookup.
      pose proof (map_Forall_lookup_1 _ _ _ _ Hlens Hlookup) as Hlen.
      simpl in Hlen.
      rewrite last_length.
      pose proof (extend_length_ge Reject n y) as Hextend.
      lia.
    }
    unfold equal_latest_proposal.
    rewrite latest_before_quorum_caccept; last done.
    destruct Heq as [? | Heq]; [by left | right].
    destruct e as [| v]; first done. simpl in Heq.
    destruct (ps !! latest_before_quorum _ _) as [psl |] eqn:Hpsk; last done.
    destruct psl; last done.
    rewrite equal_max_occurrence_caccept_iff; first done.
    apply (map_Forall_impl _ _ _ Hlens). intros _ l Hl.
    eapply Nat.lt_le_trans; last apply Hl.
    apply latest_before_quorum_lt.
    { intros Hz. by rewrite Hz latest_before_quorum_zero Hpsz in Hpsk. }
    by apply (ballots_not_empty bs).
  Qed.

  Theorem vp_inv_faccept {bs ps} x n v :
    valid_proposals bs ps ->
    valid_proposals (faccept bs x n v) ps.
  Proof.
    intros [Hpsz Hvp].
    split; first done. intros m e Hdsm.
    apply Hvp in Hdsm as (bsq & Hbsq & Hquorum & Hlens & Heq).
    exists (faccept bsq x n v).
    split; first by apply alter_mono.
    split; first by do 2 rewrite dom_alter_L.
    unfold equal_latest_proposal_or_free.
    split.
    { apply map_Forall_alter; last apply Hlens.
      intros y Hlookup.
      pose proof (map_Forall_lookup_1 _ _ _ _ Hlens Hlookup) as Hlen.
      simpl in Hlen.
      rewrite last_length.
      pose proof (extend_length_ge Reject n y) as Hextend.
      lia.
    }
    unfold equal_latest_proposal.
    rewrite latest_before_quorum_faccept; last done.
    destruct Heq as [? | Heq]; [by left | right].
    destruct e as [| v']; first done. simpl in Heq.
    destruct (ps !! latest_before_quorum _ _) as [psl |] eqn:Hpsk; last done.
    destruct psl; last done.
    rewrite equal_max_occurrence_faccept_iff; first done.
    apply (map_Forall_impl _ _ _ Hlens). intros _ l Hl.
    eapply Nat.lt_le_trans; last apply Hl.
    apply latest_before_quorum_lt.
    { intros Hz. by rewrite Hz latest_before_quorum_zero Hpsz in Hpsk. }
    by apply (ballots_not_empty bs).
  Qed.

  (**
   * Invariance of [valid_ballots].
   *)
  Theorem vb_inv_prepare {bs ps} x n :
    valid_ballots bs ps ->
    valid_ballots (prepare bs x n) ps.
  Proof.
    intros Hvb.
    apply map_Forall_alter; last apply Hvb.
    intros l Hbsx m Hacc.
    apply (Hvb x l Hbsx).
    by eapply prepare_node_accepted_in_classic.
  Qed.

  Theorem vb_inv_propose {bs ps} n v :
    ps !! n = None ->
    valid_ballots bs ps ->
    valid_ballots bs (propose ps n v).
  Proof.
    intros Hpsn Hvb.
    unfold propose.
    intros x l Hbsx n' Hacc.
    destruct (decide (n' = n)) as [-> | Hneq].
    { exfalso. specialize (Hvb _ _ Hbsx _ Hacc). naive_solver. }
    rewrite lookup_insert_ne; last done.
    by apply (Hvb x l).
  Qed.

  Theorem vb_inv_caccept {bs ps} x n :
    (∃ v, ps !! n = Some (Proposed v)) ->
    (∃ l, bs !! x = Some l ∧ length l ≤ n)%nat ->
    valid_ballots bs ps ->
    valid_ballots (caccept bs x n) ps.
  Proof.
    intros Hpsn Hlen Hvb.
    apply map_Forall_alter; last apply Hvb.
    intros l Hbsx m Hm.
    unfold valid_ballots in Hvb.
    destruct (decide (m < length (extend Reject n l))%nat) as [Hlt | Hge].
    { rewrite /accepted_in_classic lookup_app_l in Hm; last done.
      apply (Hvb x l); first apply Hbsx.
      by eapply prepare_node_accepted_in_classic.
    }
    apply not_lt in Hge.
    rewrite /accepted_in_classic lookup_app_r in Hm; last lia.
    rewrite list_lookup_singleton_Some in Hm.
    destruct Hm as [Hle _].
    destruct Hlen as (l' & Hlookup' & Hlen).
    rewrite Hlookup' in Hbsx. inversion Hbsx. subst l'.
    rewrite extend_length in Hge, Hle.
    destruct (decide (n = m)) as [Heq | Hneq]; last first.
    { clear -Hlen Hge Hle Hneq. lia. }
    by rewrite -Heq.
  Qed.

  Theorem vb_inv_faccept {bs ps} x n v :
    valid_ballots bs ps ->
    valid_ballots (faccept bs x n v) ps.
  Proof.
    intros Hvb.
    apply map_Forall_alter; last apply Hvb.
    intros l Hbsx m Hacc.
    apply (Hvb x l Hbsx).
    by eapply faccept_node_accepted_in_classic.
  Qed.

  (**
   * Invariance of [valid_consensus].
   *)
  Lemma accepted_in_classic_app_eq b n t :
    accepted_in_classic b n ->
    accepted_in_classic (b ++ t) n.
  Proof. intros Hacc. by apply lookup_app_l_Some. Qed.

  Lemma accepted_in_fast_app_eq b n v t :
    accepted_in_fast b n v ->
    accepted_in_fast (b ++ t) n v.
  Proof. intros Hacc. by apply lookup_app_l_Some. Qed.

  Theorem vc_inv_prepare {c bs ps} x n :
    valid_consensus c bs ps ->
    valid_consensus c (prepare bs x n) ps.
  Proof.
    unfold valid_consensus.
    destruct c as [v' |]; last done.
    intros [n' (Hnz & bsq & Hbsq & Hchosen)].
    exists n'.
    split; first done.
    exists (prepare bsq x n).
    split; first by apply alter_mono.
    destruct Hchosen as [(Hpsn' & Hquorum & Hacc) | (Hpsn' & Hquorum & Hacc)]; [left | right].
    { split; first done.
      split; first by do 2 rewrite dom_alter_L.
      apply map_Forall_alter; last done.
      intros y Hy.
      specialize (Hacc _ _ Hy). simpl in Hacc.
      by apply accepted_in_classic_app_eq.
    }
    { split; first done.
      split; first by do 2 rewrite dom_alter_L.
      apply map_Forall_alter; last done.
      intros y Hy.
      specialize (Hacc _ _ Hy). simpl in Hacc.
      by apply accepted_in_fast_app_eq.
    }
  Qed.

  Theorem vc_inv_propose {c bs ps} n e :
    ps !! n = None ->
    valid_consensus c bs ps ->
    valid_consensus c bs (propose ps n e).
  Proof.
    intros Hpsn. unfold valid_consensus.
    destruct c as [v |]; last done.
    intros [n' (Hnz & bsq & Hbsq & Hchosen)].
    exists n'.
    split; first done.
    exists bsq.
    split; first done.
    destruct Hchosen as [(Hpsn' & Hquorum & Hacc) | (Hpsn' & Hquorum & Hacc)]; [left | right].
    { split; last done.
      assert (Hne : n ≠ n') by set_solver.
      rewrite lookup_insert_Some. by right.
    }
    { split; last done.
      assert (Hne : n ≠ n') by set_solver.
      rewrite lookup_insert_Some. by right.
    }
  Qed.

  Theorem vc_inv_caccept {c bs ps} x n :
    valid_consensus c bs ps ->
    valid_consensus c (caccept bs x n) ps.
  Proof.
    unfold valid_consensus.
    destruct c as [v' |]; last done.
    intros [n' (Hnz & bsq & Hbsq & Hchosen)].
    exists n'.
    split; first done.
    exists (caccept bsq x n).
    split; first by apply alter_mono.
    destruct Hchosen as [(Hpsn' & Hquorum & Hacc) | (Hpsn' & Hquorum & Hacc)]; [left | right].
    { split; first done.
      split; first by do 2 rewrite dom_alter_L.
      apply map_Forall_alter; last done.
      intros y Hy.
      specialize (Hacc _ _ Hy). simpl in Hacc.
      rewrite /caccept_node -app_assoc.
      by apply accepted_in_classic_app_eq.
    }
    { split; first done.
      split; first by do 2 rewrite dom_alter_L.
      apply map_Forall_alter; last done.
      intros y Hy.
      specialize (Hacc _ _ Hy). simpl in Hacc.
      rewrite /caccept_node -app_assoc.
      by apply accepted_in_fast_app_eq.
    }
  Qed.

  Theorem vc_inv_faccept {c bs ps} x n v :
    valid_consensus c bs ps ->
    valid_consensus c (faccept bs x n v) ps.
  Proof.
    unfold valid_consensus.
    destruct c as [v' |]; last done.
    intros [n' (Hnz & bsq & Hbsq & Hchosen)].
    exists n'.
    split; first done.
    exists (faccept bsq x n v).
    split; first by apply alter_mono.
    destruct Hchosen as [(Hpsn' & Hquorum & Hacc) | (Hpsn' & Hquorum & Hacc)]; [left | right].
    { split; first done.
      split; first by do 2 rewrite dom_alter_L.
      apply map_Forall_alter; last done.
      intros y Hy.
      specialize (Hacc _ _ Hy). simpl in Hacc.
      rewrite /faccept_node -app_assoc.
      by apply accepted_in_classic_app_eq.
    }
    { split; first done.
      split; first by do 2 rewrite dom_alter_L.
      apply map_Forall_alter; last done.
      intros y Hy.
      specialize (Hacc _ _ Hy). simpl in Hacc.
      rewrite /faccept_node -app_assoc.
      by apply accepted_in_fast_app_eq.
    }
  Qed.

  (**
   * Invariance of [valid_terms].
   *)
  Definition gt_prev_term (ts : gmap A nat) (x : A) (n : nat) :=
    (∃ c, ts !! x = Some c ∧ (c < n)%nat).

  Theorem vt_inv_advance {P : A -> nat -> Prop} {ps ts x n} :
    gt_prev_term ts x n ->
    valid_terms P ps ts ->
    valid_terms P ps (advance ts x n).
  Proof.
    intros Hprev [Hdisj Hvt].
    split; first done.
    intros y u Hadv u' Hyu' Hlt.
    unfold advance in Hadv.
    destruct (decide (y = x)) as [-> | Hne]; last first.
    { rewrite lookup_insert_ne in Hadv; last done.
      by specialize (Hvt _ _ Hadv _ Hyu' Hlt).
    }
    rewrite lookup_insert in Hadv.
    inversion Hadv. subst u. clear Hadv.
    destruct Hprev as (c & Hxc & Hcn).
    assert (Hcu' : (c < u')%nat) by lia.
    by specialize (Hvt _ _ Hxc _ Hyu' Hcu').
  Qed.

  Theorem vt_inv_propose_advance {P : A -> nat -> Prop} {ps ts x n} v :
    gt_prev_term ts x n ->
    P x n ->
    valid_terms P ps ts ->
    valid_terms P (propose ps n v) (advance ts x n).
  Proof.
    rewrite /propose /advance.
    intros Hprev Hxn [Hdisj Hvt].
    split; first done.
    intros y u Hadv u' Hyu' Hlt.
    destruct (decide (y = x)) as [-> | Hne]; last first.
    { destruct (decide (u' = n)) as [-> | Hne'].
      { by specialize (Hdisj _ _ _ Hne Hyu'). }
      rewrite lookup_insert_ne in Hadv; last done.
      specialize (Hvt _ _ Hadv _ Hyu' Hlt).
      by rewrite lookup_insert_ne.
    }
    rewrite lookup_insert in Hadv.
    inversion Hadv. subst u. clear Hadv.
    rewrite lookup_insert_ne; last lia.
    destruct Hprev as (c & Hxc & Hcn).
    assert (Hcu' : (c < u')%nat) by lia.
    by specialize (Hvt _ _ Hxc _ Hyu' Hcu').
  Qed.

End pure.
