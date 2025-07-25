From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import quorum list fin_sets fin_maps extend.
From Perennial.program_proof.tulip Require Import base.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Definition proposals := gmap nat bool.

Section def.
  Context `{Countable A}.
  Implicit Type r : nat.
  Implicit Type d : bool.
  Implicit Type l : ballot.
  Implicit Type bs bsq : gmap A ballot.
  Implicit Type ps : proposals.

  Definition accepted_in l r d := l !! r = Some (Accept d).

  #[global]
  Instance accepted_in_decision l r d :
    Decision (accepted_in l r d).
  Proof. unfold accepted_in. apply _. Qed.

  Definition chosen_in_fast bs d :=
    ∃ bsq, bsq ⊆ bs ∧
           fquorum_size (dom bs) (dom bsq) ∧
           map_Forall (λ _ l, accepted_in l O d) bsq.

  Definition chosen_in_classic bs r d :=
    ∃ bsq, bsq ⊆ bs ∧
           cquorum_size (dom bs) (dom bsq) ∧
           map_Forall (λ _ l, accepted_in l r d) bsq.

  Definition chosen_in bs r d :=
    if decide (r = O) then chosen_in_fast bs d else chosen_in_classic bs r d.

  Definition chosen bs d := ∃ r, chosen_in bs r d.

  Definition stability bs :=
    ∀ d1 d2, chosen bs d1 -> chosen bs d2 -> d2 = d1.

  Definition proposed_after_chosen bs ps :=
    ∀ t1 t2 v,
    (t1 < t2)%nat ->
    chosen_in bs t1 v ->
    is_Some (ps !! t2) ->
    ps !! t2 = Some v.

  Fixpoint latest_before (n : nat) (l : ballot) : nat :=
    match n with
    | O => O
    | S k => match l !! k with
            | Some (Accept _) => k
            | _ => latest_before k l
            end
    end.

  Definition latest_before_quorum_step (x : A) (cur prev : nat) : nat :=
    cur `max` prev.

  Definition latest_before_quorum r bsq :=
    let rs := fmap (latest_before r) bsq in
    map_fold latest_before_quorum_step O rs.

  Definition nfast bs d :=
    size (filter (λ x, accepted_in x.2 O d) bs).

  Definition nfastneg bs d :=
    size (filter (λ x, not (accepted_in x.2 O d)) bs).

  Definition equal_latest_proposal_or_free bs bsq ps r d :=
    let n := latest_before_quorum r bsq in
    if decide (n = O)
    then size bs / 4 + 1 ≤ nfast bsq d
    else ps !! n = Some d.

  Definition valid_proposal bs ps r d :=
    ∃ bsq : gmap A ballot,
      bsq ⊆ bs ∧
      cquorum_size (dom bs) (dom bsq) ∧
      equal_latest_proposal_or_free bs bsq ps r d.

  Definition valid_proposals bs ps :=
    map_Forall (λ r d, valid_proposal bs ps r d) ps.

  Definition valid_ballots bs ps :=
    map_Forall (λ _ l, ∀ r d, r ≠ O -> accepted_in l r d -> ps !! r = Some d) bs.

End def.

Section stability.
  Context `{Countable A}.
  Implicit Type r : nat.
  Implicit Type d : bool.
  Implicit Type l : ballot.
  Implicit Type bs bsq : gmap A ballot.
  Implicit Type ps : proposals.

  Lemma ballots_overlapped (bs bsq1 bsq2 : gmap A ballot) :
    bsq1 ⊆ bs ->
    bsq2 ⊆ bs ->
    cquorum_size (dom bs) (dom bsq1) ->
    (cquorum_size (dom bs) (dom bsq2) ∨ fquorum_size (dom bs) (dom bsq2)) ->
    ∃ x l, bsq1 !! x = Some l ∧ bsq2 !! x = Some l.
  Proof.
    intros Hsubseteq1 Hsubseteq2 Hsize1 Hsize2.
    assert (Hq1 : cquorum (dom bs) (dom bsq1)).
    { split; last apply Hsize1. by apply subseteq_dom. }
    assert (Hq2 : cquorum (dom bs) (dom bsq2) ∨ fquorum (dom bs) (dom bsq2)).
    { destruct Hsize2 as [Hsize2 | Hsize2]; [left | right].
      { split; [by apply subseteq_dom | apply Hsize2]. }
      { split; first by apply subseteq_dom.
        split; first apply Hsize2.
        rewrite size_non_empty_iff_L.
        apply (cquorum_non_empty_c _ _ Hq1).
      }
    }
    unshelve epose proof (quorums_overlapped _ (dom bsq1) _ _ Hq2) as (x & Hin1 & Hin2).
    { by left. }
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

  Lemma latest_before_quorum_step_ge (ns : gmap A nat) :
    map_Forall (λ _ n, (n ≤ map_fold latest_before_quorum_step O ns)%nat) ns.
  Proof.
    intros x n.
    apply (map_fold_weak_ind (λ p m, (m !! x = Some n -> n ≤ p)%nat)); first done.
    intros y n' m b _ Hnr Hn'.
    unfold latest_before_quorum_step.
    destruct (decide (y = x)) as [-> | Hne].
    { rewrite lookup_insert_eq in Hn'. inversion_clear Hn'. lia. }
    rewrite lookup_insert_ne in Hn'; last done.
    specialize (Hnr Hn').
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

  Lemma latest_before_quorum_step_O_or_exists (ns : gmap A nat) :
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

  Lemma latest_before_quorum_step_in (ns : gmap A nat) :
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

  Lemma latest_before_Sn l n d :
    accepted_in l n d ->
    latest_before (S n) l = n.
  Proof. intros Hacc. by rewrite /= Hacc. Qed.

  Lemma latest_before_accepted_in l m n d :
    (m < n)%nat ->
    accepted_in l m d ->
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

  Lemma latest_before_quorum_accepted_in bs n1 n2 :
    (n1 < n2)%nat ->
    (∃ d, map_Exists (λ _ l, accepted_in l n1 d) bs) ->
    (n1 ≤ latest_before_quorum n2 bs < n2)%nat.
  Proof.
    intros Hn (d & x & l & Hlookup & Hacc).
    split.
    { pose proof (latest_before_quorum_ge bs n2) as Hlargest.
      rewrite map_Forall_lookup in Hlargest.
      specialize (Hlargest _ _ Hlookup).
      pose proof (latest_before_accepted_in _ _ _ _ Hn Hacc) as Hle.
      clear -Hlargest Hle. lia.
    }
    assert (Hnonempty : bs ≠ ∅) by set_solver.
    destruct (latest_before_quorum_in bs n2 Hnonempty) as (y & ly & _ & <-).
    apply latest_before_lt.
    lia.
  Qed.

  Lemma latest_before_quorum_lt bs n :
    bs ≠ ∅ ->
    n ≠ O ->
    (latest_before_quorum n bs < n)%nat.
  Proof.
    intros Hnonempty.
    destruct (latest_before_quorum_in bs n Hnonempty) as (y & ly & _ & <-).
    apply latest_before_lt.
  Qed.

  Lemma nfast_nfastneg_complement bs v :
    (nfast bs v + nfastneg bs v)%nat = size bs.
  Proof.
    rewrite -map_size_disj_union.
    { by rewrite map_filter_union_complement. }
    apply map_disjoint_filter_complement.
  Qed.

  Lemma vp_vb_impl_pac bs ps :
    valid_proposals bs ps ->
    valid_ballots bs ps ->
    proposed_after_chosen bs ps.
  Proof.
    intros Hvp Hvb r1 r2 d Hlt Hchosen Hr2.
    (* Strong induction on [r2]. *)
    induction (lt_wf r2) as [r _ IH].
    destruct Hr2 as [d' Hd'].
    edestruct Hvp as (bsq1 & Hincl1 & Hquorum1 & Heq).
    { apply Hd'. }
    rewrite /chosen_in in Hchosen.
    assert (∃ bsq2, bsq2 ⊆ bs ∧
                    map_Forall (λ _ l, accepted_in l r1 d) bsq2 ∧
                    (if decide (r1 = O)
                     then fquorum_size (dom bs) (dom bsq2)
                     else cquorum_size (dom bs) (dom bsq2)))
      as (bsq2 & Hincl2 & Hacc & Hquorum2).
    { case_decide as Hr1.
      { destruct Hchosen as (bsq & Hincl & Hfq & Hacc). subst r1. by eauto. }
      { destruct Hchosen as (bsq & Hincl & Hcq & Hacc). by eauto. }
    }
    edestruct ballots_overlapped as (x & l & Hbsq1 & Hbsq2).
    { apply Hincl1. }
    { apply Hincl2. }
    { apply Hquorum1. }
    { case_decide; [by right | by left]. }
    unshelve epose proof (latest_before_quorum_accepted_in bsq1 r1 r _ _) as Horder.
    { apply Hlt. }
    { specialize (Hacc _ _ Hbsq2).
      exists d.
      rewrite map_Exists_lookup.
      by eauto.
    }
    rewrite /equal_latest_proposal_or_free in Heq.
    set k := latest_before_quorum _ _ in Horder Heq.
    destruct (decide (r1 = k)) as [Hr1k | Hr1k]; last first.
    { (* Case: [r1 < k < r]. *)
      assert (Hk : (r1 < k < r)%nat) by lia. clear Horder Hr1k.
      destruct (decide (k = O)) as [Hz | Hnz].
      { clear -Hz Hk. lia. }
      unshelve epose proof (IH k _ _ _) as Hd; [lia | lia | done |].
      rewrite Hd in Heq. by inv Heq.
    }
    (* Case: [r1 = k]. *)
    clear Horder.
    subst r1.
    case_decide as Hk.
    { (* Fast rank. *)
      rewrite Hk in Hacc.
      destruct (decide (d' = d)) as [-> | Hne]; first apply Hd'.
      rewrite /nfast in Heq.
      set bsq3 := filter _ bsq1 in Heq.
      assert (Hincl : bsq3 ⊆ bs).
      { trans bsq1; [apply map_filter_subseteq | apply Hincl1]. }
      assert (hcquorum (dom bs) (dom bsq3)) as Hhcq.
      { split; first apply subseteq_dom, Hincl.
        rewrite /hcquorum_size 2!size_dom.
        lia.
      }
      unshelve epose proof (hcquorum_fquorum_overlapped _ _ (dom bsq2) Hhcq _)
        as (y & Hin1 & Hin2).
      { by split; first apply subseteq_dom. }
      apply elem_of_dom in Hin1 as [l1 Hl1].
      apply elem_of_dom in Hin2 as [l2 Hl2].
      assert (l2 = l1) as ->.
      { pose proof (lookup_weaken _ _ _ _ Hl1 Hincl) as Hbsy1.
        pose proof (lookup_weaken _ _ _ _ Hl2 Hincl2) as Hbsy2.
        rewrite Hbsy1 in Hbsy2.
        by inv Hbsy2.
      }
      subst bsq3.
      apply map_lookup_filter_Some in Hl1 as [Hl1 Hacc']. simpl in Hacc'.
      specialize (Hacc _ _ Hl2). simpl in Hacc.
      rewrite /accepted_in Hacc in Hacc'.
      inv Hacc'.
    }
    { (* Classic rank. *)
      specialize (Hacc _ _ Hbsq2). simpl in Hacc.
      pose proof (lookup_weaken _ _ _ _ Hbsq1 Hincl1) as Hl.
      specialize (Hvb _ _ Hl _ _ Hk Hacc).
      rewrite Hvb in Heq. by inv Heq.
    }
  Qed.

  Lemma chosen_in_vb_pac_eq bs ps r1 r2 d1 d2 :
    (r1 < r2)%nat ->
    chosen_in bs r1 d1 ->
    chosen_in bs r2 d2 ->
    valid_ballots bs ps ->
    proposed_after_chosen bs ps ->
    d2 = d1.
  Proof.
    intros Hlt Hd1 Hd2 Hvb Hpac.
    assert (Hps : ps !! r2 = Some d2).
    { rewrite /chosen_in in Hd2.
      case_decide as Hr2; first lia.
      destruct Hd2 as (bsq & Hincl & Hcq & Hacc).
      unshelve epose proof (cquorum_non_empty_q (dom bs) (dom bsq) _) as Hne.
      { by split; first apply subseteq_dom. }
      apply set_choose_L in Hne as [x Hx].
      apply elem_of_dom in Hx as [l Hl].
      specialize (Hacc _ _ Hl). simpl in Hacc.
      pose proof (lookup_weaken _ _ _ _ Hl Hincl) as Hin.
      by specialize (Hvb _ _ Hin _ _ Hr2 Hacc).
    }
    unshelve epose proof (Hpac _ _ _ Hlt Hd1 _) as Hps'; first done.
    rewrite Hps in Hps'.
    by inv Hps'.
  Qed.

  Lemma vb_pac_impl_stability bs ps :
    valid_ballots bs ps ->
    proposed_after_chosen bs ps ->
    stability bs.
  Proof.
    intros Hvb Hpac d1 d2 [r1 Hchosen1] [r2 Hchosen2].
    destruct (decide (r1 < r2)%nat) as [Hlt | Hge].
    { by eapply chosen_in_vb_pac_eq. }
    destruct (decide (r2 = r1)) as [-> | Hne]; last first.
    { assert (r2 < r1)%nat as Hlt by lia.
      symmetry.
      by eapply chosen_in_vb_pac_eq.
    }
    assert (∃ bsq, bsq ⊆ bs ∧
                   (cquorum_size (dom bs) (dom bsq) ∨ fquorum_size (dom bs) (dom bsq)) ∧
                   map_Forall (λ _ l, accepted_in l r1 d1) bsq)
             as (bsq1 & Hincl1 & Hsize1 & Hacc1).
    { rewrite /chosen_in in Hchosen1.
      case_decide as Hr; destruct Hchosen1 as (bsq & Hincl & Hsize & Hacc).
      { subst r1. exists bsq. split; first done. by split; first right. }
      { exists bsq. split; first done. by split; first left. }
    }
    assert (∃ bsq, bsq ⊆ bs ∧
                   (cquorum_size (dom bs) (dom bsq) ∨ fquorum_size (dom bs) (dom bsq)) ∧
                   map_Forall (λ _ l, accepted_in l r1 d2) bsq)
             as (bsq2 & Hincl2 & Hsize2 & Hacc2).
    { rewrite /chosen_in in Hchosen2.
      case_decide as Hr; destruct Hchosen2 as (bsq & Hincl & Hsize & Hacc).
      { subst r1. exists bsq. split; first done. by split; first right. }
      { exists bsq. split; first done. by split; first left. }
    }
    unshelve epose proof (quorums_overlapped (dom bs) (dom bsq1) (dom bsq2) _ _)
      as (x & Hin1 & Hin2).
    { destruct Hsize1.
      { left. by split; first apply subseteq_dom. }
      { right. by split; first apply subseteq_dom. }
    }
    { destruct Hsize2.
      { left. by split; first apply subseteq_dom. }
      { right. by split; first apply subseteq_dom. }
    }
    apply elem_of_dom in Hin1 as [l1 Hl1].
    apply elem_of_dom in Hin2 as [l2 Hl2].
    specialize (Hacc1 _ _ Hl1). simpl in Hacc1.
    specialize (Hacc2 _ _ Hl2). simpl in Hacc2.
    assert (Hleq : l1 = l2).
    { eapply lookup_weaken in Hl1; last apply Hincl1.
      eapply lookup_weaken in Hl2; last apply Hincl2.
      rewrite Hl1 in Hl2. by inv Hl2.
    }
    subst l2.
    rewrite /accepted_in Hacc1 in Hacc2.
    by inv Hacc2.
  Qed.

  Theorem vp_vb_impl_stability bs ps :
    valid_proposals bs ps ->
    valid_ballots bs ps ->
    stability bs.
  Proof.
    intros Hvp Hvb.
    eapply vb_pac_impl_stability; first apply Hvb.
    by apply vp_vb_impl_pac.
  Qed.

End stability.

Section lemma.
  Context `{Countable A}.
  Implicit Type r : nat.
  Implicit Type d : bool.
  Implicit Type l : ballot.
  Implicit Type bs bsq : gmap A ballot.
  Implicit Type ps : proposals.

  (** Lemmas used by users of stability. *)

  Lemma chosen_in_fast_agree bs d1 d2 :
    chosen_in_fast bs d1 ->
    chosen_in_fast bs d2 ->
    d2 = d1.
  Proof.
    intros (bsq1 & Hincl1 & Hq1 & Hacc1) (bsq2 & Hincl2 & Hq2 & Hacc2).
    pose proof (quorums_overlapped (dom bs) (dom bsq1) (dom bsq2))
      as (rid & Hin1 & Hin2).
    { right. by split; first apply subseteq_dom. }
    { right. by split; first apply subseteq_dom. }
    apply elem_of_dom in Hin1 as [l1 Hl1].
    apply elem_of_dom in Hin2 as [l2 Hl2].
    specialize (Hacc1 _ _ Hl1). simpl in Hacc1.
    specialize (Hacc2 _ _ Hl2). simpl in Hacc2.
    pose proof (lookup_weaken _ _ _ _ Hl1 Hincl1) as Hbsl1.
    pose proof (lookup_weaken _ _ _ _ Hl2 Hincl2) as Hbsl2.
    rewrite Hbsl2 in Hbsl1. inv Hbsl1.
    rewrite /accepted_in Hacc2 in Hacc1.
    by inv Hacc1.
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

  Lemma latest_before_quorum_eq bs bslb n :
    map_Forall (λ _ l, (n ≤ length l)%nat) bslb ->
    map_Forall2 (λ _ lb l, prefix lb l) bslb bs ->
    latest_before_quorum n bs = latest_before_quorum n bslb.
  Proof.
    intros Hlen Hprefix.
    apply map_Forall2_forall in Hprefix as [Hprefix Hdom].
    unfold latest_before_quorum.
    replace (latest_before n <$> bs) with (latest_before n <$> bslb); first done.
    rewrite map_eq_iff.
    intros x.
    rewrite 2!lookup_fmap.
    (* Why does the following fail? *)
    (* destruct (dom_eq_lookup x Hdom) as [[[l Hl] [lb Hlb]] | [-> ->]]. *)
    destruct (dom_eq_lookup x Hdom) as [[[lb Hlb] [l Hl]] | [Hbslb Hbsl]]; last first.
    { by rewrite Hbslb Hbsl. }
    rewrite Hlb Hl.
    simpl.
    f_equal.
    specialize (Hlen _ _ Hlb). simpl in Hlen.
    specialize (Hprefix _ _ _  Hlb Hl).
    destruct Hprefix as [tail ->].
    symmetry.
    by apply latest_before_append_eq.
  Qed.

  Lemma nfast_eq bs bslb d :
    map_Forall (λ _ l, (length l ≠ O)%nat) bslb ->
    map_Forall2 (λ _ lb l, prefix lb l) bslb bs ->
    nfast bs d = nfast bslb d.
  Proof.
    intros Hlen.
    generalize dependent bs.
    induction bslb as [| x lb bslb Hnone IH] using map_ind.
    { intros bs Hprefix.
      apply map_Forall2_dom_L in Hprefix.
      rewrite dom_empty_L in Hprefix. symmetry in Hprefix.
      apply dom_empty_inv_L in Hprefix.
      by subst bs.
    }
    intros bs Hprefix.
    apply map_Forall2_dom_L in Hprefix as Hdom.
    assert (is_Some (bs !! x)) as [l Hl].
    { rewrite -elem_of_dom -Hdom dom_insert_L. set_solver. }
    rewrite /nfast -(insert_delete_id bs x l Hl).
    apply map_Forall2_insert_inv_l in Hprefix; last apply Hnone.
    destruct Hprefix as (l' & bsnx & -> & Hbsn & Hprefixlb & Hprefix).
    rewrite lookup_insert_eq in Hl. inv Hl.
    apply map_Forall_insert in Hlen as [Hlenlb Hlen]; last apply Hnone.
    rewrite 2!map_filter_insert.
    case_decide as Hcasel.
    { case_decide as Hcaselb.
      { rewrite map_size_insert_None; last first.
        { rewrite map_lookup_filter_None. left. apply lookup_delete_eq. }
        rewrite map_size_insert_None; last first.
        { rewrite map_lookup_filter_None. left. apply Hnone. }
        f_equal.
        apply IH; [apply Hlen | by rewrite delete_insert_id].
      }
      exfalso.
      unshelve epose proof (prefix_lookup_lt lb l O _ Hprefixlb) as Hlookup.
      { clear -Hlenlb. lia. }
      by rewrite /accepted_in Hlookup Hcasel in Hcaselb.
    }
    { case_decide as Hcaselb; last first.
      { rewrite delete_delete_eq delete_insert_id; last apply Hbsn.
        rewrite delete_id; last apply Hnone.
        by apply IH.
      }
      exfalso.
      pose proof (prefix_lookup_Some _ _ _ _ Hcaselb Hprefixlb) as Hlookup.
      by rewrite /accepted_in Hlookup in Hcasel.
    }
  Qed.

  Lemma equal_latest_proposal_or_free_eq bs bsq bsqlb ps n d :
    n ≠ O ->
    map_Forall (λ _ l, (n ≤ length l)%nat) bsqlb ->
    map_Forall2 (λ _ lb l, prefix lb l) bsqlb bsq ->
    equal_latest_proposal_or_free bs bsq ps n d =
    equal_latest_proposal_or_free bs bsqlb ps n d.
  Proof.
    intros Hnz Hlen Hprefix.
    rewrite /equal_latest_proposal_or_free.
    rewrite (latest_before_quorum_eq _ bsqlb); last first.
    { apply Hprefix. }
    { apply Hlen. }
    case_decide as Hn; last done.
    rewrite (nfast_eq _ bsqlb); last first.
    { apply Hprefix. }
    { intros x l Hl. specialize (Hlen _ _ Hl). simpl in Hlen.
      clear -Hlen Hnz. lia.
    }
    apply map_Forall2_dom_L in Hprefix.
    done.
    (* by rewrite -(size_dom bs) -(size_dom bslb) Hprefix. *)
  Qed.

  Definition latest_term (l : ballot) := latest_before (length l) l.

  Lemma latest_term_snoc_Accept (l : ballot) p :
    latest_term (l ++ [Accept p]) = length l.
  Proof. by rewrite /latest_term last_length /= lookup_snoc_length. Qed.

  Lemma latest_term_singleton v :
    latest_term [v] = O.
  Proof. rewrite /latest_term /=. by destruct v. Qed.

  Lemma latest_term_snoc_Reject (l : ballot) :
    latest_term (l ++ [Reject]) = latest_term l.
  Proof.
    rewrite /latest_term last_length /=.
    rewrite lookup_snoc_length.
    by apply latest_before_append_eq.
  Qed.

  Lemma latest_term_extend_Reject (n : nat) (l : ballot) :
    latest_term (extend n Reject l) = latest_term l.
  Proof.
    unfold extend.
    induction n as [| n' IHn']; first by rewrite app_nil_r.
    destruct (decide (n' < length l)%nat) as [Hlt | Hge].
    { replace (n' - length l)%nat with O in IHn' by lia.
      by replace (S n' - length l)%nat with O by lia.
    }
    replace (S n' - length l)%nat with (S (n' - length l)%nat) by lia.
    by rewrite replicate_S_end assoc latest_term_snoc_Reject.
  Qed.

  Lemma latest_term_length_lt (l : ballot) :
    l ≠ [] ->
    (latest_term l < length l)%nat.
  Proof. intros Hnnil. by apply latest_before_lt, length_not_nil. Qed.

End lemma.
