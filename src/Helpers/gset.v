From stdpp Require Import gmap.
From Coq Require Import ssreflect.

Lemma gset_elem_is_empty `{Countable A} (c:gset A) :
  (forall x, x ∉ c) →
  c = ∅.
Proof.
  intros Hnoelem.
  apply set_eq; intros.
  split; intros Helem.
  - contradiction (Hnoelem x).
  - contradiction (not_elem_of_empty (C:=gset A) x).
Qed.

Lemma set_split_element `{!EqDecision L, !Countable L} (d: gset L) a :
  a ∈ d →
  d = {[a]} ∪ (d ∖ {[a]}).
Proof.
  intros.
  apply set_eq; intros a'.
  destruct (decide (a = a')); set_solver.
Qed.
