From Coq Require Import Lists.List.
From stdpp Require Import list sets.

From Coq Require Import ssreflect.

Lemma Forall_subset {A} f (l1: list A) (l2: list A) :
  l1 ⊆ l2 →
  Forall f l2 →
  Forall f l1.
Proof.
  intros Hsubset Hl2.
  apply List.Forall_forall.
  intros x Hin_l1.
  apply elem_of_list_In in Hin_l1.
  destruct (elem_of_subseteq l1 l2) as (Hsubset_elem_of&_).
  apply Hsubset_elem_of with (x := x) in Hsubset; intuition.
  destruct (List.Forall_forall f l2) as (Hl2_impl&_).
  apply elem_of_list_In in Hsubset.
  apply (Hl2_impl Hl2 x) in Hsubset.
  done.
Qed.

Lemma list_app_subseteq {A} (l1 l2 l : list A) :
  l1 ++ l2 ⊆ l ↔ l1 ⊆ l ∧ l2 ⊆ l.
Proof.
  set_solver.
Qed.

Lemma list_cons_subseteq {A} (x: A) (l1 l2: list A) :
  x :: l1 ⊆ l2 ↔ x ∈ l2 ∧ l1 ⊆ l2.
Proof. set_solver. Qed.

Lemma elem_of_subseteq_concat {A} (x:list A) (l:list (list A)) :
  x ∈ l → x ⊆ concat l.
Proof.
  intros Helem.
  apply elem_of_list_split in Helem as (l1 & l2 & ->).
  rewrite concat_app concat_cons.
  set_solver.
Qed.

Lemma concat_respects_subseteq {A} (l1 l2: list (list A)) :
  l1 ⊆ l2 →
  concat l1 ⊆ concat l2.
Proof.
  generalize dependent l2.
  induction l1 as [|x l1]; intros; simpl.
  - set_solver.
  - apply list_cons_subseteq in H as [Helem ?].
    apply list_app_subseteq. split; [|by eauto].
    apply elem_of_subseteq_concat; auto.
Qed.

Lemma list_fmap_mono {A B} (f: A → B) (l1 l2: list A) :
  l1 ⊆ l2 → f <$> l1 ⊆ f <$> l2.
Proof.
  intros Hsubseteq.
  apply (iffRL (elem_of_subseteq _ _)).
  intros y Hin.
  destruct (elem_of_list_fmap_2 _ _ _ Hin) as (x&Hy&Hx).
  apply ((iffLR (elem_of_subseteq _ _)) Hsubseteq x) in Hx.
  apply (elem_of_list_fmap_1_alt _ _ _ _ Hx Hy).
Qed.

Lemma drop_subseteq {A} (l: list A) n :
  drop n l ⊆ l.
Proof.
  intros x.
  rewrite !elem_of_list_lookup.
  setoid_rewrite lookup_drop.
  naive_solver.
Qed.
