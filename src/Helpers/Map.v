From stdpp Require Import gmap.
From Coq Require Import ssreflect.

From Perennial.Helpers Require Import gset.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Section map.
Context {K V : Type}.
Context `{Countable K}.
Implicit Types (m : gmap K V).

Lemma map_union_dom_pair_eq (m0 m1 m2 m3 : gmap K V) :
  m0 ∪ m1 = m2 ∪ m3 →
  m0 ##ₘ m1 →
  m2 ##ₘ m3 →
  dom m0 = dom m2 →
  dom m1 = dom m3 →
  m0 = m2 ∧ m1 = m3.
Proof.
  intros Heq0 **. split; apply map_eq; intros i;
    opose proof (proj1 (map_eq_iff _ _) Heq0 i) as Heq1.
  - destruct (m0 !! i) eqn:Hm0.
    + erewrite lookup_union_Some_l in Heq1; [|exact Hm0].
      destruct (m2 !! i) eqn:Hm2; [by simpl_map|].
      apply elem_of_dom_2 in Hm0.
      apply not_elem_of_dom in Hm2.
      set_solver.
    + erewrite lookup_union_r in Heq1; [|done].
      destruct (m2 !! i) eqn:Hm2; [|done].
      apply elem_of_dom_2 in Hm2.
      apply not_elem_of_dom in Hm0.
      set_solver.
  - destruct (m1 !! i) eqn:Hm1.
    + erewrite lookup_union_Some_r in Heq1; [|done|exact Hm1].
      destruct (m3 !! i) eqn:Hm3; [by simpl_map|].
      apply elem_of_dom_2 in Hm1.
      apply not_elem_of_dom in Hm3.
      set_solver.
    + erewrite lookup_union_l in Heq1; [|done].
      destruct (m3 !! i) eqn:Hm3; [|done].
      apply elem_of_dom_2 in Hm3.
      apply not_elem_of_dom in Hm1.
      set_solver.
Qed.

Lemma destruct_map_pair_dom_eq {V1} (m0 m1 : gmap K V) (m2 m3 : gmap K V1) :
  dom m0 = dom m2 →
  dom m1 = dom m3 →
  (∀ k : K,
    (is_Some (m0 !! k) ∧ is_Some (m2 !! k)) ∨
    (m0 !! k = None ∧ is_Some (m1 !! k) ∧ m2 !! k = None ∧ is_Some (m3 !! k)) ∨
    ((m0 ∪ m1) !! k = None ∧ (m2 ∪ m3) !! k = None)).
Proof.
  intros. rewrite -!elem_of_dom -!not_elem_of_dom.
  destruct (decide (k ∈ dom m0)), (decide (k ∈ dom m1)); set_solver.
Qed.

Lemma map_Forall2_union {V1} P (m0 m1 : gmap K V) (m2 m3 : gmap K V1) :
  map_Forall2 P m0 m2 →
  map_Forall2 P m1 m3 →
  map_Forall2 P (m0 ∪ m1) (m2 ∪ m3).
Proof.
  intros HM0 HM1 k.
  opose proof (map_Forall2_dom_L _ _ _ HM0) as Hdom0.
  opose proof (map_Forall2_dom_L _ _ _ HM1) as Hdom1.
  opose proof (destruct_map_pair_dom_eq _ _ _ _ Hdom0 Hdom1 k) as Hd.
  destruct_or?; destruct_and?.
  - by rewrite !lookup_union_l'.
  - by rewrite !lookup_union_r.
  - rewrite H0 H1. constructor.
Qed.

End map.

Section map.

Context (K V:Type).
Context `{Countable K}.
Notation gmap := (gmap K V).
Implicit Types (m:gmap).

Lemma map_difference_union' m1 m2 :
  m1 ∖ m2 ∪ m2 = m2 ∪ m1.
Proof.
  apply map_eq. intros i.
  apply option_eq. intros v.
  unfold difference, map_difference, difference_with, map_difference_with.
  rewrite !lookup_union_Some_raw !lookup_merge.
  destruct (m1 !! i) as [x'|], (m2 !! i); compute; intuition congruence.
Qed.

Lemma size_list_to_map (l : list (K * V)) :
  NoDup l.*1 →
  size (list_to_map l : gmap) = length l.
Proof.
  intros Hnodup. rewrite <-size_dom, dom_list_to_map.
  rewrite size_list_to_set //. rewrite length_fmap. done.
Qed.

Lemma map_subset_dom_eq m m' :
  dom m = dom m' →
  m' ⊆ m →
  m = m'.
Proof.
  intros Hdom Hsub.
  apply map_eq => l.
  apply option_eq => v.
  split.
  - intros.
    assert (l ∈ dom m') as [v' ?]%elem_of_dom.
    { rewrite -Hdom.
      apply elem_of_dom; eauto. }
    rewrite H1.
    eapply map_subseteq_spec in H1; eauto.
    congruence.
  - apply map_subseteq_spec; auto.
Qed.

End map.

Theorem imap_NoDup {A B} (f: nat → A → B) (l: list A) :
  (∀ i1 x1 i2 x2,
      i1 ≠ i2 →
      l !! i1 = Some x1 →
      l !! i2 = Some x2 →
      f i1 x1 ≠ f i2 x2) →
  NoDup (imap f l).
Proof.
  revert f.
  induction l as [|x l]; simpl; intros f Hfneq.
  - constructor.
  - constructor.
    + intros Helem%elem_of_lookup_imap_1.
      destruct Helem as (i'&x'&[Heq Hlookup]).
      apply Hfneq in Heq; eauto.
    + apply IHl; intros.
      eapply Hfneq; eauto.
Qed.

Lemma length_gmap_to_list `{Countable K} `(m: gmap K A) :
  length (map_to_list m) = size m.
Proof.
  induction m using map_ind.
  - rewrite map_to_list_empty //.
  - rewrite map_to_list_insert /= //.
    rewrite map_size_insert_None /= // IHm //.
Qed.

Lemma map_size_filter `{Countable K} `(m: gmap K A) P `{∀ x, Decision (P x)} :
  size (filter P m) ≤ size m.
Proof.
  induction m using map_ind.
  - rewrite map_filter_empty //.
  - rewrite map_size_insert_None //.
    destruct (decide (P (i, x))).
    + rewrite map_filter_insert_True //.
      rewrite map_size_insert_None.
      { apply map_lookup_filter_None_2; auto. }
      lia.
    + rewrite map_filter_insert_not' //.
      { congruence. }
      lia.
Qed.

Lemma map_size_dom `{Countable K} `(m: gmap K A) :
  size m = size (dom m).
Proof.
  induction m using map_ind.
  - rewrite dom_empty_L !map_size_empty //.
  - rewrite dom_insert_L.
    rewrite map_size_insert_None //.
    rewrite size_union.
    { apply not_elem_of_dom in H0.
      set_solver. }
    rewrite size_singleton.
    lia.
Qed.

Lemma map_size_nonzero `{Countable K} `(m: gmap K A) a :
  is_Some (m !! a) →
  (0 < size m)%nat.
Proof.
  destruct 1 as [v Hlookup].
  induction m using map_ind.
  - rewrite lookup_empty in Hlookup; congruence.
  - rewrite map_size_insert_None //. lia.
Qed.

Lemma map_size_nonzero_lookup `{Countable K} `(m: gmap K A) a v :
  m !! a = Some v →
  (0 < size m)%nat.
Proof.
  eauto using map_size_nonzero.
Qed.
