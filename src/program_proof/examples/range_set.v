From Coq Require Import ssreflect.
From stdpp Require Import gmap fin_sets.
From Perennial.Helpers Require Import Integers.

Set Default Proof Using "Type".

Definition rangeSet (start sz: Z): gset u64 :=
  list_to_set (U64 <$> seqZ start sz).

Lemma elem_of_seq start sz :
  ∀ i, i ∈ seq start sz ↔ (start ≤ i < start + sz)%nat.
Proof.
  intros i.
  rewrite elem_of_list_In in_seq.
  auto.
Qed.

Lemma elem_of_seqZ start sz :
  ∀ i, i ∈ seqZ start sz ↔ start ≤ i < start + sz.
Proof.
  intros i.
  rewrite /seqZ.
  rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_seq.
  split; intros.
  - destruct H as [y [-> Hin]]; lia.
  - exists (Z.to_nat (i - start)); lia.
Qed.

Theorem rangeSet_lookup (start sz: Z) (i: u64) :
  0 ≤ start →
  start + sz < 2^64 →
  i ∈ rangeSet start sz ↔ start ≤ int.val i < start + sz.
Proof.
  intros Hpos Hoverflow.
  rewrite /rangeSet.
  rewrite elem_of_list_to_set.
  rewrite elem_of_list_fmap.
  split; intros.
  - destruct H as [y [-> Hin%elem_of_seqZ]]; word.
  - exists (int.val i).
    split; [ word | ].
    apply elem_of_seqZ; word.
Qed.

(* TODO: upstream this *)
Lemma gset_eq `{Countable A} (c1 c2: gset A) :
  (forall (x:A), x ∈ c1 ↔ x ∈ c2) → c1 = c2.
Proof.
  intros Hexteq.
  destruct c1 as [c1], c2 as [c2].
  f_equal.
  apply map_eq.
  rewrite /elem_of /gset_elem_of/mapset.mapset_elem_of /= in Hexteq.
  intros.
  destruct (c1 !! i) eqn:Hc1;
    destruct (c2 !! i) eqn:Hc2; auto.
  - destruct u, u0; auto.
  - destruct u; apply Hexteq in Hc1.
    congruence.
  - destruct u; apply Hexteq in Hc2.
    congruence.
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

Lemma rangeSet_diag (start sz: Z) :
  sz = 0 ->
  rangeSet start sz = ∅.
Proof.
  intros.
  rewrite /rangeSet.
  rewrite H.
  auto.
Qed.

Lemma rangeSet_set_size (start sz: Z) :
  start + sz < 2^64 →
  set_size (rangeSet start sz) = Z.to_nat sz.
Proof.
  rewrite /set_size.
  rewrite /rangeSet.
  rewrite /seqZ.
  generalize dependent (Z.to_nat sz); intros sz'.
  (* TODO: this seems hard; perhaps it would be fruitful to try a more
  extensional strategy that uses the lookup theorem above to characterize
  elements ∘ list_to_set (as a permutation of the underlying list, if NoDup) and
  then look at the length of that list *)
Admitted.
