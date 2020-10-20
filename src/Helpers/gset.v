From stdpp Require Import gmap.
From Coq Require Import ssreflect.

(* TODO: upstream this *)
Lemma gset_eq `{Countable A} (c1 c2: gset A) :
  (forall (x:A), x ∈ c1 ↔ x ∈ c2) → c1 = c2.
Proof.
  intros Hexteq.
  destruct c1 as [c1], c2 as [c2].
  f_equal.
  apply map_eq.
  unfold elem_of, gset_elem_of, mapset.mapset_elem_of in Hexteq.
  simpl in Hexteq.
  intros.
  destruct (c1 !! i) eqn:Hc1;
    destruct (c2 !! i) eqn:Hc2;
    repeat match goal with u: unit |- _ => destruct u end; auto.
  - apply Hexteq in Hc1; congruence.
  - apply Hexteq in Hc2; congruence.
Qed.

Lemma gset_elem_is_empty `{Countable A} (c:gset A) :
  (forall x, x ∉ c) →
  c = ∅.
Proof.
  intros Hnoelem.
  apply gset_eq; intros.
  split; intros Helem.
  - contradiction (Hnoelem x).
  - contradiction (not_elem_of_empty (C:=gset A) x).
Qed.

Lemma set_split_element `{!EqDecision L, !Countable L} (d: gset L) a :
  a ∈ d →
  d = {[a]} ∪ (d ∖ {[a]}).
Proof.
  intros.
  apply gset_eq; intros a'.
  destruct (decide (a = a')); set_solver.
Qed.
