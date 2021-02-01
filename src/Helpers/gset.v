From stdpp Require Import gmap.
From Coq Require Import ssreflect.

(* TODO: upstream this, see std++ MR 210. *)
Lemma gset_eq `{Countable A} (c1 c2: gset A) :
  (forall (x:A), x ∈ c1 ↔ x ∈ c2) → c1 = c2.
Proof. apply set_eq. Qed.

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
