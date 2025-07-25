From Coq Require Import ssreflect.
From stdpp Require Import gmap fin_sets.
From Perennial.Helpers Require Import gset.
From Perennial.Helpers Require Import Integers.

Definition rangeSet (start sz: Z): gset u64 :=
  list_to_set (W64 <$> seqZ start sz).

Theorem rangeSet_lookup (start sz: Z) (i: u64) :
  0 ≤ start →
  start + sz < 2^64 →
  i ∈ rangeSet start sz ↔ start ≤ uint.Z i < start + sz.
Proof.
  intros Hpos Hoverflow.
  rewrite /rangeSet.
  rewrite elem_of_list_to_set.
  rewrite list_elem_of_fmap.
  split; intros.
  - destruct H as [y [-> Hin%elem_of_seqZ]]; word.
  - exists (uint.Z i).
    split; [ word | ].
    apply elem_of_seqZ; word.
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

Lemma rangeSet_empty (start sz: Z) :
  sz ≤ 0 →
  rangeSet start sz = ∅.
Proof.
  intros. rewrite /rangeSet seqZ_nil //.
Qed.

Lemma rangeSet_size (start sz: Z) :
  0 ≤ start →
  0 ≤ sz →
  start + sz < 2^64 →
  size (rangeSet start sz) = Z.to_nat sz.
Proof.
  rewrite /size /set_size.
  rewrite /rangeSet.
  intros Hnonneg1 Hnonneg2 Hoverflow.
  replace start with (Z.of_nat (Z.to_nat start)) in * by lia.
  replace sz with (Z.of_nat (Z.to_nat sz)) in * by lia.
  generalize dependent (Z.to_nat sz); intros sz'. clear sz.
  generalize dependent (Z.to_nat start); intros start'. clear start.
  rewrite ?Nat2Z.id.
  generalize dependent start'.
  induction sz'; intros; simpl.
  - reflexivity.
  - rewrite -> seqZ_cons by lia. simpl.
    rewrite -> elements_union_singleton.
    + rewrite <- (IHsz' (S start')) at 2 by lia.
      simpl. repeat f_equal; lia.
    + intro H.
      eapply rangeSet_lookup in H; try lia.
      intuition idtac. revert H0. word.
Qed.

Lemma rangeSet_append_one:
  ∀ start sz : u64,
    uint.Z start + uint.Z sz < 2 ^ 64
    → ∀ i : u64,
      uint.Z i < uint.Z (word.add start sz)
      → uint.Z start ≤ uint.Z i
      → {[i]} ∪ rangeSet (uint.Z start) (uint.Z i - uint.Z start) =
        rangeSet (uint.Z start) (uint.Z i - uint.Z start + 1).
Proof.
  intros start sz Hbound i Hibound Hilower_bound.
  replace (uint.Z (word.add start sz)) with (uint.Z start + uint.Z sz) in Hibound by word.
  apply set_eq; intros.
  rewrite elem_of_union.
  rewrite elem_of_singleton.
  rewrite !rangeSet_lookup; try word.
Qed.

Lemma rangeSet_first:
  ∀ start sz,
    sz > 0 ->
    rangeSet start sz = {[W64 start]} ∪ rangeSet (start+1) (sz-1).
Proof.
  rewrite /rangeSet.
  intros.
  rewrite seqZ_cons; [|lia].
  simpl.
  reflexivity.
Qed.

Lemma rangeSet_first_disjoint start sz :
  0 ≤ start →
  start + sz < 2^64 →
  {[W64 start]} ## (rangeSet (start+1) (sz-1)).
Proof.
  intros Hnonneg1 Hoverflow x Hin1 Hin2.
  assert (x = W64 start) by set_solver.
  subst. apply rangeSet_lookup in Hin2; eauto; try word.
Qed.
