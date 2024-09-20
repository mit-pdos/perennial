From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import quorum list.
From Perennial.program_proof.tulip.paxos Require Import base.

Section lemma.
  Context `{Countable A}.
  Context `{Lookup nat B M}.
  Implicit Type t n : nat.
  Implicit Type l : proposals.
  Implicit Type v : ledger.
  Implicit Type bs bsq : gmap A proposals.
  Implicit Type ps psb : proposals.
  Implicit Type m : M.
  Implicit Type ms : gmap A M.
  Implicit Type f : option B -> option ledger.

  Lemma vub_chosen_in_proposed bs ps t v :
    valid_ub_ballots bs ps ->
    chosen_in bs t v ->
    ∃ v', ps !! t = Some v' ∧ prefix v v'.
  Proof.
    intros Hub (bsq & Hincl & Hquorum & Hacc).
    unshelve epose proof (cquorum_non_empty_q (dom bs) (dom bsq) _) as Hne.
    { by apply subseteq_dom in Hincl. }
    rewrite dom_empty_iff_L in Hne.
    apply map_choose in Hne as (i & l & Hl).
    specialize (Hacc _ _ Hl). simpl in Hacc.
    destruct Hacc as (u & Hu & Hprefix).
    rewrite map_subseteq_spec in Hincl.
    specialize (Hincl _ _ Hl).
    specialize (Hub _ _ Hincl _ _ Hu).
    destruct Hub as (v' & Hps & Huv').
    exists v'.
    split; first apply Hps.
    by trans u.
  Qed.

  Lemma vub_pac_chosen_in_prefix bs ps t1 t2 v1 v2 :
    (t1 ≤ t2)%nat ->
    valid_ub_ballots bs ps ->
    proposed_after_chosen bs ps ->
    chosen_in bs t1 v1 ->
    chosen_in bs t2 v2 ->
    prefix v1 v2 ∨ prefix v2 v1.
  Proof.
    intros Hle Hvub Hpac Hchosen1 Hchosen2.
    destruct (vub_chosen_in_proposed _ _ _ _ Hvub Hchosen2) as (v & Hv & Hprefix).
    destruct (decide (t1 = t2)) as [Heq | Hne].
    { destruct (vub_chosen_in_proposed _ _ _ _ Hvub Hchosen1) as (v' & Hv' & Hprefix').
      subst t2. rewrite Hv in Hv'. symmetry in Hv'. inv Hv'.
      by eapply prefix_common_ub.
    }
    assert (Hlt : (t1 < t2)%nat) by lia.
    specialize (Hpac _ _ _ _ Hlt Hchosen1 Hv).
    by eapply prefix_common_ub.
  Qed.

  Lemma vub_pac_impl_consistency bs ps psb :
    valid_ub_ballots bs ps ->
    valid_proposals ps psb ->
    proposed_after_chosen bs psb ->
    consistency bs.
  Proof.
    intros Hvub Hvp Hpacb.
    assert (Hpac : proposed_after_chosen bs ps).
    { intros t1 t2 v1 v2 Hlt Hchosen Hv2.
      specialize (Hvp t2).
      rewrite Hv2 in Hvp.
      destruct (psb !! t2) as [vlb |] eqn:Heq; rewrite Heq in Hvp; last done.
      simpl in Hvp.
      specialize (Hpacb _ _ _ _ Hlt Hchosen Heq).
      by trans vlb.
    }
    intros v1 v2 [t1 Hchosen1] [t2 Hchosen2].
    destruct (decide (t1 ≤ t2)%nat) as [Hle | Hgt].
    { by eapply vub_pac_chosen_in_prefix. }
    { assert (Hge : (t2 ≤ t1)%nat) by lia.
      rewrite base.or_comm.
      by eapply vub_pac_chosen_in_prefix.
    }
  Qed.

  Lemma ballots_overlapped bs bsq1 bsq2 :
    bsq1 ⊆ bs ->
    bsq2 ⊆ bs ->
    cquorum_size (dom bs) (dom bsq1) ->
    cquorum_size (dom bs) (dom bsq2) ->
    ∃ x l, bsq1 !! x = Some l ∧ bsq2 !! x = Some l.
  Proof.
    intros Hsubseteq1 Hsubseteq2 Hsize1 Hsize2.
    unshelve epose proof (quorums_overlapped (dom bs) (dom bsq1) (dom bsq2) _ _)
      as (x & Hin1 & Hin2).
    { left. split; last apply Hsize1. by apply subseteq_dom. }
    { left. split; last apply Hsize2. by apply subseteq_dom. }
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

  Lemma longest_proposal_spec (ovs : gmap A (option ledger)) :
    match longest_proposal ovs with
    | Some vlg => map_Exists (λ _ ov, ov = Some vlg) ovs ∧
                 map_Forall (λ _ ov, match ov with
                                     | Some v => (length v ≤ length vlg)%nat
                                     | None => True
                                     end) ovs
    | None => map_Forall (λ _ ov, ov = None) ovs
    end.
  Proof.
    rewrite /longest_proposal.
    induction ovs as [| x ov ovs Hnone Hfold IH] using map_first_key_ind.
    { by rewrite map_fold_empty. }
    rewrite map_fold_insert_first_key; [| apply Hnone | apply Hfold].
    destruct (map_fold _ _ _) as [vprev |]; last first.
    { (* Case: No previous proposal. *)
      simpl.
      destruct ov as [v |]; last first.
      { by apply map_Forall_insert. }
      (* Case: Current proposal [v] exists. *)
      split.
      { exists x, (Some v). by rewrite lookup_insert. }
      { apply map_Forall_insert; first done.
        split; first lia.
        intros y ov Hov.
        specialize (IH _ _ Hov).
        by rewrite IH.
      }
    }
    (* Case: Previous proposal [vprev] exists. *)
    simpl.
    destruct IH as [Hexists Hlongest].
    destruct ov as [v |]; last first.
    { (* Case: No current proposal. *)
      split.
      { by apply map_Exists_insert_2_2. }
      { by apply map_Forall_insert. }
    }
    (* Case: Current proposal [v] exists. *)
    case_decide as Hlength; last first.
    { (* Case: Previous proposal longer than the current one. *)
      rewrite Nat.nlt_ge in Hlength.
      split.
      { by apply map_Exists_insert_2_2. }
      { by rewrite map_Forall_insert. }
    }
    (* Case: Current proposal longer than the previous one. *)
    split.
    { by apply map_Exists_insert_2_1. }
    rewrite map_Forall_insert; last done.
    split; first done.
    apply (map_Forall_impl _ _ _ Hlongest).
    intros _ ov.
    destruct ov; [lia | done].
  Qed.

  Lemma longest_proposal_in_term_with_spec f ms t :
    match longest_proposal_in_term_with f ms t with
    | Some v => map_Exists (λ _ m, f (m !! t) = Some v) ms ∧
               map_Forall (λ _ m, match f (m !! t) with
                                  | Some v' => (length v' ≤ length v)%nat
                                  | _ => True
                                  end) ms
    | None => map_Forall (λ _ m, f (m !! t) = None) ms
    end.
  Proof.
    rewrite /longest_proposal_in_term_with.
    set ovs := fmap _ _.
    pose proof (longest_proposal_spec ovs) as Hovs.
    destruct (longest_proposal ovs) as [v |]; last first.
    { (* Case: No proposal. *)
      intros x l Hl.
      rewrite map_Forall_fmap in Hovs.
      specialize (Hovs _ _ Hl). simpl in Hovs.
      by rewrite /ledger_at_term_with in Hovs.
    }
    (* Case: Longest proposal [v] exists. *)
    destruct Hovs as [Hexists Hlongest].
    split.
    { destruct Hexists as (x & ov & Hov & ->).
      rewrite lookup_fmap in Hov.
      destruct (ms !! x) as [l |] eqn:Hl; last done.
      rewrite /= /ledger_at_term_with in Hov.
      (* destruct (l !! t) as [d |] eqn:Hd; last done. *)
      (* destruct d as [v' |]; last done. *)
      inv Hov.
      by exists x, l.
    }
    { intros x l Hl.
      rewrite map_Forall_fmap in Hlongest.
      by specialize (Hlongest _ _ Hl).
    }
  Qed.

  Lemma longest_proposal_in_term_Some f ms t v :
    longest_proposal_in_term_with f ms t = Some v ->
    map_Exists (λ _ m, f (m !! t) = Some v) ms ∧
    map_Forall (λ _ m, match f (m !! t) with
                       | Some v' => (length v' ≤ length v)%nat
                       | _ => True
                       end) ms.
  Proof.
    intros Hv.
    pose proof (longest_proposal_in_term_with_spec f ms t) as Hspec.
    by rewrite Hv in Hspec.
  Qed.

  Lemma latest_before_quorum_step_O_or_exists (ts : gmap A nat) :
    map_fold latest_term_before_quorum_step O ts = O ∨
    ∃ x, ts !! x = Some (map_fold latest_term_before_quorum_step O ts).
  Proof.
    apply (map_fold_weak_ind (λ p r, p = O ∨ ∃ x, r !! x = Some p)); first by left.
    intros x n m b Hmx IHm.
    unfold latest_term_before_quorum_step.
    destruct IHm as [-> | [y Hy]]; right.
    { exists x. rewrite lookup_insert. by rewrite Nat.max_0_r. }
    destruct (decide (b ≤ n)%nat).
    { exists x. rewrite lookup_insert. by replace (_ `max` _)%nat with n by lia. }
    exists y.
    assert (Hne : x ≠ y) by set_solver.
    rewrite lookup_insert_ne; last done. rewrite Hy.
    by replace (_ `max` _)%nat with b by lia.
  Qed.

  Lemma latest_term_before_quorum_step_ge (ts : gmap A nat) :
    map_Forall (λ _ t, (t ≤ map_fold latest_term_before_quorum_step O ts)%nat) ts.
  Proof.
    intros x t.
    apply (map_fold_weak_ind (λ p r, (r !! x = Some t -> t ≤ p)%nat)); first done.
    intros y n m b _ Hnr Hn.
    unfold latest_term_before_quorum_step.
    destruct (decide (y = x)) as [-> | Hne].
    { rewrite lookup_insert in Hn. inversion_clear Hn. lia. }
    rewrite lookup_insert_ne in Hn; last done.
    specialize (Hnr Hn).
    lia.
  Qed.

  Lemma latest_term_before_quorum_ge f ms t :
    map_Forall
      (λ _ (m : M), (latest_term_before_with f t m ≤ latest_term_before_quorum_with f ms t)%nat)
      ms.
  Proof.
    intros x l Hlookup.
    unfold latest_term_before_quorum_with.
    pose proof (latest_term_before_quorum_step_ge (latest_term_before_with f t <$> ms)) as Hstep.
    rewrite map_Forall_lookup in Hstep.
    apply (Hstep x (latest_term_before_with f t l)).
    rewrite lookup_fmap.
    by rewrite Hlookup.
  Qed.

  Lemma latest_before_quorum_step_in (ts : gmap A nat) :
    ts ≠ ∅ ->
    map_Exists (λ _ t, t = map_fold latest_term_before_quorum_step O ts) ts.
  Proof.
    intros Hnonempty.
    destruct (latest_before_quorum_step_O_or_exists ts) as [Hz | [x Hx]]; last first.
    { exists x. by eauto. }
    rewrite Hz.
    destruct (decide (O ∈ (map_img ts : gset nat))) as [Hin | Hnotin].
    { rewrite elem_of_map_img in Hin.
      destruct Hin as [x Hx].
      by exists x, O.
    }
    assert (Hallgz : ∀ t, t ∈ (map_img ts : gset nat) -> (0 < t)%nat).
    { intros t Ht. assert (Hnz : t ≠ O) by set_solver. lia. }
    apply map_choose in Hnonempty.
    destruct Hnonempty as (x & n & Hxn).
    apply latest_term_before_quorum_step_ge in Hxn as Hle.
    rewrite Hz in Hle.
    apply (elem_of_map_img_2 (SA:=gset nat)) in Hxn.
    apply Hallgz in Hxn.
    lia.
  Qed.

  Lemma latest_term_before_quorum_in f ms t :
    ms ≠ ∅ ->
    map_Exists
      (λ _ (m : M), (latest_term_before_with f t m = latest_term_before_quorum_with f ms t)%nat)
      ms.
  Proof.
    intros Hnonempty.
    unfold latest_term_before_quorum_with.
    pose proof (latest_before_quorum_step_in (latest_term_before_with f t <$> ms)) as Hstep.
    rewrite fmap_empty_iff in Hstep.
    specialize (Hstep Hnonempty).
    destruct Hstep as (x & m & Hlookup & <-).
    rewrite lookup_fmap fmap_Some in Hlookup.
    destruct Hlookup as (l & Hlookup & Heq).
    by exists x, l.
  Qed.

  Lemma latest_term_before_le f m t :
    (latest_term_before_with f t m ≤ t)%nat.
  Proof.
    induction t as [| t IH]; first by simpl.
    simpl.
    destruct (f (m !! t)) as [v |]; lia.
  Qed.

  Lemma latest_term_before_mono f m t1 t2 :
    (t1 ≤ t2)%nat ->
    (latest_term_before_with f t1 m ≤ latest_term_before_with f t2 m)%nat.
  Proof.
    intros Ht.
    induction t2 as [| t2 IH].
    { assert (Ht1 : (t1 = 0)%nat); first lia. by rewrite Ht1. }
    destruct (decide (t1 = S t2)) as [-> | Hne]; first done.
    unshelve epose proof (IH _) as Hle; first lia.
    simpl.
    destruct (f (m !! t2)) as [v |]; last by eauto.
    etrans; first apply Hle.
    apply latest_term_before_le.
  Qed.

  Lemma latest_term_before_Some f m t1 t2 :
    (t1 < t2)%nat ->
    (∃ v, f (m !! t1) = Some v) ->
    (t1 ≤ latest_term_before_with f t2 m)%nat.
  Proof.
    intros Hmn Hacc.
    assert (Ht1 : latest_term_before_with f (S t1) m = t1).
    { destruct Hacc as [v Hv].
      by rewrite /latest_term_before_with Hv.
    }
    rewrite -Ht1.
    apply latest_term_before_mono.
    lia.
  Qed.

  Lemma latest_term_before_lt f m t :
    t ≠ O ->
    (latest_term_before_with f t m < t)%nat.
  Proof.
    induction t as [| t IHt]; first by simpl.
    intros _.
    destruct (decide (t = O)) as [-> | Hneq].
    { simpl. destruct (f (m !! O)) as [v |]; lia. }
    specialize (IHt Hneq).
    simpl.
    destruct (f (m !! t)) as [v |]; lia.
  Qed.

  Lemma latest_term_before_quorum_with_Some f ms t1 t2 :
    (t1 < t2)%nat ->
    map_Exists (λ _ m, ∃ v, f (m !! t1) = Some v) ms ->
    (t1 ≤ latest_term_before_quorum_with f ms t2 < t2)%nat.
  Proof.
    intros Hn (x & l & Hlookup & Hacc).
    pose proof (latest_term_before_quorum_ge f ms t2) as Hlargest.
    rewrite map_Forall_lookup in Hlargest.
    specialize (Hlargest _ _ Hlookup).
    pose proof (latest_term_before_Some _ _ _ _ Hn Hacc) as Hle.
    split; first lia.
    assert (Hnonempty : ms ≠ ∅) by set_solver.
    destruct (latest_term_before_quorum_in f ms t2 Hnonempty) as (y & ly & _ & <-).
    apply latest_term_before_lt.
    lia.
  Qed.

End lemma.

Section impl.
  Context `{Countable A}.

  Lemma vlb_vbp_impl_pac (bs : gmap A proposals) (ps psb : proposals) :
    valid_lb_ballots bs psb ->
    valid_ub_ballots bs ps ->
    valid_base_proposals bs psb ->
    proposed_after_chosen bs psb.
  Proof.
    intros Hvlb Hvub Hvbp t1 t2 v1 v2 Hlt Hchosen Hv2.
    (* Strong induction on [t2]. *)
    generalize dependent v2.
    induction (lt_wf t2) as [t2 _ IH].
    intros v2 Hv2.
    (* Obtain first quorum from [valid_base_proposals]. *)
    specialize (Hvbp _ _ Hv2). simpl in Hvbp.
    destruct Hvbp as (bsq2 & Hincl2 & Hqm2 & Hlongest).
    rewrite /equal_latest_longest_proposal in Hlongest.
    (* Obtain second quorum from [chosen_in]. *)
    destruct Hchosen as (bsq1 & Hincl1 & Hqm1 & Hacc).
    pose proof (ballots_overlapped _ _ _ Hincl1 Hincl2 Hqm1 Hqm2) as (x & l & Hbsq1 & Hbsq2).
    specialize (Hacc _ _ Hbsq1). simpl in Hacc.
    destruct Hacc as (v & Hv & Hprefix).
    (* Obtain [t1 ≤ latest_term_before_quorum bsq1 t2 < t2] *)
    unshelve epose proof (latest_term_before_quorum_with_Some id bsq2 _ _ Hlt _) as Ht.
    { exists x, l. by eauto. }
    set t := latest_term_before_quorum_with _ _ _ in Ht, Hlongest.
    apply longest_proposal_in_term_Some in Hlongest as [Hexists Hlongest].
    destruct Hexists as (x2 & l2 & Hl2 & Hl2t).
    pose proof (lookup_weaken _ _ _ _ Hl2 Hincl2) as Hbsx2.
    destruct (decide (t1 = t)) as [-> | Hne].
    { (* Case [t1 = t]. Derive [prefix v v2] from [Hlongest] and [Hprefix]. *)
      trans v; first apply Hprefix.
      specialize (Hlongest _ _ Hbsq2). simpl in Hlongest.
      rewrite Hv in Hlongest.
      (* Obtain a common upper bound using [Hvub] to derive [prefix v v2]. *)
      apply Hvub in Hbsx2.
      specialize (Hbsx2 _ _ Hl2t).
      destruct Hbsx2 as (vub & Hub & Hleub).
      pose proof (lookup_weaken _ _ _ _ Hbsq1 Hincl1) as Hbsx.
      apply Hvub in Hbsx.
      specialize (Hbsx _ _ Hv).
      destruct Hbsx as (vub' & Hub' & Hleub').
      rewrite Hub in Hub'. symmetry in Hub'. inv Hub'.
      pose proof (prefix_common_ub _ _ _ Hleub Hleub') as Hvv2.
      destruct Hvv2 as [Hvv2 | ?]; last done.
      by rewrite (prefix_length_eq _ _ Hvv2 Hlongest).
    }
    specialize (Hvlb _ _ Hbsx2 _ _ Hl2t).
    destruct Hvlb as (v' & Hv' & Hprefix').
    trans v'; last apply Hprefix'.
    apply (IH t); [lia | lia | done].
  Qed.

  Theorem vlb_vbp_impl_consistency (bs : gmap A proposals) (ps psb : proposals) :
    valid_lb_ballots bs psb ->
    valid_ub_ballots bs ps ->
    valid_base_proposals bs psb ->
    valid_proposals ps psb ->
    consistency bs.
  Proof.
    intros Hvlb Hvub Hvbp Hvp.
    pose proof (vlb_vbp_impl_pac _ _ _ Hvlb Hvub Hvbp) as Hpac.
    by eapply vub_pac_impl_consistency.
  Qed.

End impl.
