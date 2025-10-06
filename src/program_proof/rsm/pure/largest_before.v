From iris.proofmode Require Import proofmode.
From Perennial.program_proof.rsm.pure Require Export nat.

Definition largest_step (n : nat) (r : option nat) :=
  match r with
  | Some x => if decide (n < x)%nat then r else Some n
  | _ => Some n
  end.

Definition largest (ns : gset nat) :=
  set_fold largest_step None ns.

Lemma largest_spec ns :
  match largest ns with
  | Some n => n ∈ ns ∧ ge_all n ns
  | None => ns = ∅
  end.
Proof.
  set P := λ (r : option nat) (xs : gset nat),
             match r with
             | Some n => n ∈ xs ∧ ge_all n xs
             | None => xs = ∅
             end.
  apply (set_fold_ind_L P); first done.
  intros x xs r Hnotin HP.
  subst P.
  destruct r as [n |]; simpl; last first.
  { split; first set_solver.
    by rewrite /ge_all HP union_empty_r_L set_Forall_singleton.
  }
  destruct HP as [Hn Hxs].
  case_decide.
  { split; first set_solver.
    apply set_Forall_union; last done.
    rewrite set_Forall_singleton.
    lia.
  }
  split; first set_solver.
  apply set_Forall_union.
  { by rewrite set_Forall_singleton. }
  apply (set_Forall_impl _ _ _ Hxs).
  intros y Hy.
  lia.
Qed.

Definition largest_before (n : nat) (ns : gset nat) :=
  largest (filter (λ x, x ≤ n)%nat ns).

Lemma largest_before_spec n ns :
  match largest_before n ns with
  | Some p => p ∈ ns ∧ (p ≤ n)%nat ∧ outside_all p n ns
  | None => lt_all n ns
  end.
Proof.
  rewrite /largest_before.
  set nsf := filter _ _.
  pose proof (largest_spec nsf) as Hspec.
  destruct (largest _) as [p |] eqn:Hns; last first.
  { intros x Hx.
    apply not_ge.
    intros Hgt.
    set_solver.
  }
  destruct Hspec as [Hp Hnsf].
  split; first set_solver.
  split; first set_solver.
  intros x Hx.
  destruct (decide (x ≤ n)%nat) as [Hxn | Hnx].
  - left. apply Hnsf. by rewrite elem_of_filter.
  - right. lia.
Qed.

Lemma largest_before_Some n p ns :
  largest_before n ns = Some p ->
  p ∈ ns ∧ (p ≤ n)%nat ∧ outside_all p n ns.
Proof.
  intros Hlargest.
  pose proof (largest_before_spec n ns) as Hspec.
  by rewrite Hlargest in Hspec.
Qed.

Lemma largest_before_None n ns :
  largest_before n ns = None ->
  lt_all n ns.
Proof.
  intros Hlargest.
  pose proof (largest_before_spec n ns) as Hspec.
  by rewrite Hlargest in Hspec.
Qed.

Lemma largest_before_elem_of n ns :
  n ∈ ns ->
  largest_before n ns = Some n.
Proof.
  intros Hn.
  pose proof (largest_before_spec n ns) as Hspec.
  destruct (largest_before _ _) as [p |] eqn:Hns; last first.
  { specialize (Hspec _ Hn). simpl in Hspec. lia. }
  destruct Hspec as (Hp & Hpn & Hout).
  specialize (Hout _ Hn). simpl in Hout.
  destruct Hout; last lia.
  assert (n = p) by lia.
  by subst n.
Qed.

Lemma largest_before_not_elem_of n ns :
  n ∉ ns ->
  largest_before n ns = largest_before (pred n) ns.
Proof.
  intros Hnotin.
  pose proof (largest_before_spec n ns) as Hn.
  pose proof (largest_before_spec (pred n) ns) as Hpredn.
  destruct (largest_before n ns) as [p |], (largest_before (pred n) ns) as [q |].
  - destruct Hn as (Hp & Hple & Houtsidep).
    destruct Hpredn as (Hq & Hqle & Houtsideq).
    specialize (Houtsidep _ Hq). simpl in Houtsidep.
    specialize (Houtsideq _ Hp). simpl in Houtsideq.
    f_equal.
    assert (Hne : n ≠ p) by set_solver.
    clear -Hple Houtsidep Hqle Houtsideq Hne. lia.
  - destruct Hn as (Hp & Hle & _).
    assert (Hne : n ≠ p) by set_solver.
    specialize (Hpredn _ Hp). simpl in Hpredn.
    clear -Hle Hpredn Hne. lia.
  - destruct Hpredn as (Hq & Hle & _).
    specialize (Hn _ Hq). simpl in Hn.
    clear -Hle Hn. lia.
  - done.
Qed.

Lemma largest_before_empty n :
  largest_before n ∅ = None.
Proof.
  destruct (largest_before _ _) as [p |] eqn:Hp; last done.
  apply largest_before_Some in Hp.
  set_solver.
Qed.

Lemma largest_before_ge_max n nmax ns :
  (nmax ≤ n) ->
  nmax ∈ ns ->
  ge_all nmax ns ->
  largest_before n ns = Some nmax.
Proof.
  intros Hn Hin Hge.
  pose proof (largest_before_spec n ns) as Hspec.
  destruct (largest_before n ns) as [p |] eqn:Hp; last first.
  { specialize (Hspec _ Hin). simpl in Hspec. lia. }
  destruct Hspec as (Hpin & Hple & Houtside).
  specialize (Hge _ Hpin). simpl in Hge.
  specialize (Houtside _ Hin). simpl in Houtside.
  destruct Houtside as [Hle | ?]; last lia.
  f_equal. lia.
Qed.

Lemma largest_before_difference_min n nmin ns :
  le_all nmin ns ->
  is_Some (largest_before n (ns ∖ {[ nmin ]})) ->
  largest_before n (ns ∖ {[ nmin ]}) = largest_before n ns.
Proof.
  intros Hle [p Hp].
  rewrite Hp.
  apply largest_before_Some in Hp as (Hpin & Hpn & Hpout).
  rewrite elem_of_difference not_elem_of_singleton in Hpin.
  destruct Hpin as [Hpin Hpne].
  destruct (largest_before n ns) as [q |] eqn:Hq; last first.
  { exfalso.
    apply largest_before_None in Hq.
    specialize (Hq _ Hpin). simpl in Hq.
    lia.
  }
  apply largest_before_Some in Hq as (Hqin & Hqn & Hqout).
  f_equal.
  apply dec_stable. intros Hne.
  specialize (Hqout _ Hpin). simpl in Hqout.
  destruct Hqout as [Hpq | ?]; last lia.
  assert (Hlt : (p < q)%nat) by lia. clear Hpq Hne.
  assert (Hqne : q ≠ nmin).
  { intros Hq. subst q.
    specialize (Hle _ Hpin). simpl in Hle.
    lia.
  }
  assert (Hq : q ∈ ns ∖ {[ nmin ]}).
  { by rewrite elem_of_difference not_elem_of_singleton. }
  specialize (Hpout _ Hq). simpl in Hpout.
  lia.
Qed.

Lemma largest_before_union_max n nmax ns :
  (n < nmax)%nat ->
  gt_all nmax ns ->
  largest_before n ({[ nmax ]} ∪ ns) = largest_before n ns.
Proof.
  intros Hn Hgt.
  rewrite /largest_before.
  rewrite filter_union_L filter_singleton_False_L; last lia.
  by rewrite union_empty_l_L.
Qed.
