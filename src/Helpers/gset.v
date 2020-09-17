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

Lemma dom_union_inv `{!EqDecision L, !Countable L} {V} (m: gmap L V) (d1 d2: gset L) :
  d1 ## d2 →
  dom (gset L) m = d1 ∪ d2 →
  ∃ m1 m2, m1 ##ₘ m2 ∧ m = m1 ∪ m2 ∧ dom _ m1 = d1 ∧ dom _ m2 = d2.
Proof.
  revert d1 d2.
  induction m as [|a v m] using map_ind; intros.
  - exists ∅, ∅.
    rewrite left_id_L.
    split_and!; [ apply map_disjoint_empty_l | set_solver .. ].
  - pose proof (iffRL (not_elem_of_dom _ _) H) as Ha_not_dom.
    rewrite dom_insert_L in H1.
    wlog: d1 d2 H0 H1 / (gset_elem_of a d1).
    { intros.
      assert (a ∈ d1 ∨ a ∈ d2) by set_solver.
      intuition eauto.
      destruct (x d2 d1) as (m1&m2&?); auto.
      - rewrite (comm_L _ d2 d1) //.
      - exists m2, m1.
        intuition auto.
        rewrite map_union_comm //. }
    intros.
    rewrite (set_split_element d1 a) // in H1 |- *.
    rewrite -assoc_L in H1.
    apply union_cancel_l_L in H1; [ | set_solver.. ].
    (* assert (dom _ m = d1 ∖ {[a]} ∪ d2) by set_solver. *)
    apply IHm in H1 as (m1&m2&?); [ | set_solver ]; intuition idtac.
    exists (<[a:=v]> m1), m2.
    split_and!; auto.
    + apply map_disjoint_dom.
      set_solver.
    + rewrite -insert_union_l.
      congruence.
    + set_solver.
Qed.
