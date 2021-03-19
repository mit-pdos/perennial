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
    rewrite map_size_insert_None /= //.
Qed.
