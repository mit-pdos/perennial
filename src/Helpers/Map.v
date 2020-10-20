From stdpp Require Import gmap.
From Coq Require Import ssreflect.

From Perennial.Helpers Require Import gset.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Section map.

  Context (K V:Type).
  Context `{Countable K}.
  Notation gmap := (gmap K V).
  Implicit Types (m:gmap).

  Theorem delete_insert_union m1 m2 k v :
    m1 !! k = Some v ->
    delete k m1 ∪ <[k := v]> m2 = m1 ∪ m2.
  Proof.
    intros.
    rewrite -insert_delete.
    rewrite -insert_union_r; first by apply lookup_delete.
    erewrite <- (insert_id (m1 ∪ m2)) by ( apply lookup_union_Some_l; eauto ).
    rewrite <- (insert_delete (m1 ∪ m2)).
    rewrite delete_union.
    eauto.
  Qed.

  Theorem map_empty_subseteq m : ∅ ⊆ m.
  Proof.
    rewrite map_subseteq_spec => k v.
    intros []%lookup_empty_Some.
  Qed.

  Lemma union_singleton_l_insert k v m :
    {[k := v]} ∪ m = <[k := v]> m.
  Proof.
    apply map_eq => k'.
    apply option_eq => v'.
    destruct (decide (k = k')); subst.
    - rewrite lookup_insert.
      erewrite lookup_union_Some_l; eauto.
      rewrite lookup_singleton_Some //.
    - rewrite lookup_insert_ne //.
      erewrite lookup_union_r; eauto.
      rewrite lookup_singleton_None //.
  Qed.

Lemma dom_union_inv m (d1 d2: gset K) :
  d1 ## d2 →
  dom (gset K) m = d1 ∪ d2 →
  ∃ m1 m2, m1 ##ₘ m2 ∧ m = m1 ∪ m2 ∧ dom _ m1 = d1 ∧ dom _ m2 = d2.
Proof.
  revert d1 d2.
  induction m as [|a v m] using map_ind; intros.
  - exists ∅, ∅.
    rewrite left_id_L.
    split_and!; [ apply map_disjoint_empty_l | set_solver .. ].
  - pose proof (iffRL (not_elem_of_dom _ _) H0) as Ha_not_dom.
    rewrite dom_insert_L in H2.
    wlog: d1 d2 H1 H2 / (gset_elem_of a d1).
    { intros.
      assert (a ∈ d1 ∨ a ∈ d2) by set_solver.
      intuition eauto.
      destruct (x d2 d1) as (m1&m2&?); auto.
      - rewrite (comm_L _ d2 d1) //.
      - exists m2, m1.
        intuition auto.
        rewrite map_union_comm //. }
    intros.
    rewrite (set_split_element d1 a) // in H2 |- *.
    rewrite -assoc_L in H2.
    apply union_cancel_l_L in H2; [ | set_solver.. ].
    (* assert (dom _ m = d1 ∖ {[a]} ∪ d2) by set_solver. *)
    apply IHm in H2 as (m1&m2&?); [ | set_solver ]; intuition idtac.
    exists (<[a:=v]> m1), m2.
    split_and!; auto.
    + apply map_disjoint_dom.
      set_solver.
    + rewrite -insert_union_l.
      congruence.
    + set_solver.
Qed.

Lemma dom_map_to_list m :
  dom (gset _) m = list_to_set (map_to_list m).*1.
Proof.
  induction m as [|l v m] using map_ind.
  - rewrite dom_empty_L map_to_list_empty //.
  - rewrite map_to_list_insert //.
    rewrite dom_insert_L.
    rewrite fmap_cons /=.
    rewrite -IHm //.
Qed.

Lemma dom_singleton_inv m a :
  dom (gset _) m = {[a]} →
  ∃ v, m = {[a := v]}.
Proof.
  intros.
  destruct (m !! a) eqn:He.
  2: {
    cut (a ∈ dom (gset _) m); [|set_solver].
    rewrite elem_of_dom He.
    intros [x ?]; congruence.
  }
  exists v. rewrite -insert_empty.
  apply map_eq; intros.
  destruct (decide (i = a)); subst.
  - rewrite lookup_insert; eauto.
  - rewrite lookup_insert_ne; eauto.
    rewrite lookup_empty.
    apply not_elem_of_dom. set_solver.
Qed.

Lemma map_subset_dom_eq m m' :
  dom (gset _) m = dom (gset _) m' →
  m' ⊆ m →
  m = m'.
Proof.
  intros Hdom Hsub.
  apply map_eq => l.
  apply option_eq => v.
  split.
  - intros.
    assert (l ∈ dom (gset _) m') as [v' ?]%elem_of_dom.
    { rewrite -Hdom.
      apply elem_of_dom; eauto. }
    rewrite H1.
    eapply map_subseteq_spec in H1; eauto.
    congruence.
  - apply map_subseteq_spec; auto.
Qed.

End map.

(** turn a list into a gmap from its indices to values *)
(* TODO: upstream this? *)
Definition list_to_imap {A} (l: list A) : gmap nat A :=
  list_to_map (imap (λ i x, (i, x)) l).

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

Theorem lookup_list_to_imap_Some {A} l (i: nat) (x: A) :
  l !! i = Some x <-> list_to_imap l !! i = Some x.
Proof.
  rewrite /list_to_imap.
  revert i.
  induction l; simpl; intros.
  - auto.
  - destruct i; simpl.
    + rewrite lookup_insert //.
    + rewrite -> lookup_insert_ne by lia.
      rewrite IHl.
      split.
      * intros Helem%elem_of_list_to_map_2%elem_of_lookup_imap_1.
        destruct Helem as (i'&x'&[Heq Hlookup]).
        inversion Heq; subst; clear Heq.
        apply elem_of_list_to_map_1.
        { rewrite fmap_imap.
          simpl.
          apply imap_NoDup; intros; simpl.
          auto. }
        change (S i', x') with (((λ (i : nat) (x : A), (i, x)) ∘ S) i' x').
        eapply elem_of_lookup_imap_2; eauto.
      * intros Helem%elem_of_list_to_map_2%elem_of_lookup_imap_1.
        destruct Helem as (i'&x'&[Heq Hlookup]).
        inversion Heq; subst; clear Heq.
        apply elem_of_list_to_map_1.
        { rewrite fmap_imap.
          simpl.
          apply imap_NoDup; intros; simpl.
          auto. }
        eapply elem_of_lookup_imap_2; eauto.
Qed.

(** a theorem that essentially fully characterizes [list_to_imap l] in terms of
    lookups (one the one hand gmap lookups, on the other list lookup) *)
Theorem lookup_list_to_imap {A} (l: list A) (i: nat) :
  list_to_imap l !! i = l !! i.
Proof.
  destruct (l !! i) eqn:Hl.
  - apply lookup_list_to_imap_Some in Hl; auto.
  - destruct (list_to_imap l !! i) eqn:Himapl; auto.
    apply lookup_list_to_imap_Some in Himapl; congruence.
Qed.

Theorem list_to_imap_app1 {A} (l: list A) (y: A) :
  list_to_imap (l ++ [y]) = <[length l := y]> (list_to_imap l).
Proof.
  apply map_eq_iff; intros.
  rewrite lookup_list_to_imap.
  destruct (decide (i < length l)%nat);
    [ | destruct (decide (i = length l)); subst ].
  - rewrite -> lookup_app_l by lia.
    rewrite -> lookup_insert_ne by lia.
    rewrite lookup_list_to_imap //.
  - rewrite -> lookup_app_r by lia.
    replace (length l - length l)%nat with 0%nat by lia.
    rewrite /= lookup_insert //.
  - rewrite -> lookup_insert_ne by lia.
    rewrite lookup_list_to_imap.
    rewrite -> lookup_app_r by lia.
    replace (i - length l)%nat with (S (i - length l - 1))%nat by lia; simpl.
    rewrite lookup_nil.
    rewrite -> lookup_ge_None_2 by lia.
    auto.
Qed.

Lemma map_difference_delete `{Countable K} {V} (a b : gmap K V) (k : K) (v : V) :
  a !! k = Some v ->
  a ∖ delete k b = <[k := v]> (a ∖ b).
Proof.
  intros.
  eapply map_eq.
  intros.
  destruct (decide (k = i)); subst.
  { rewrite lookup_insert.
    eapply lookup_difference_Some; intuition eauto.
    rewrite lookup_delete; eauto. }
  rewrite lookup_insert_ne; eauto.
  destruct ((a ∖ b) !! i) eqn:He.
  { apply lookup_difference_Some in He.
    apply lookup_difference_Some.
    intuition eauto. rewrite lookup_delete_ne; eauto. }
  apply lookup_difference_None in He.
  apply lookup_difference_None.
  intuition eauto. rewrite lookup_delete_ne; eauto.
Qed.

Lemma map_difference_empty `{Countable K} {V} (m : gmap K V) :
  m ∖ ∅ = m.
Proof.
  apply map_eq; intros.
  destruct (m !! i) eqn:He.
  - eapply lookup_difference_Some; intuition eauto.
  - eapply lookup_difference_None; intuition eauto.
Qed.
