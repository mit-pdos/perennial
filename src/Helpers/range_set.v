From Coq Require Import ssreflect.
From stdpp Require Import gmap fin_sets.
From Perennial.Helpers Require Import gset.
From Perennial.Helpers Require Import Integers.

Definition rangeSet (start sz: Z): gset u64 :=
  list_to_set (U64 <$> seqZ start sz).

Theorem rangeSet_lookup (start sz: Z) (i: u64) :
  0 ≤ start →
  start + sz < 2^64 →
  i ∈ rangeSet start sz ↔ start ≤ int.Z i < start + sz.
Proof.
  intros Hpos Hoverflow.
  rewrite /rangeSet.
  rewrite elem_of_list_to_set.
  rewrite elem_of_list_fmap.
  split; intros.
  - destruct H as [y [-> Hin%elem_of_seqZ]]; word.
  - exists (int.Z i).
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
    rewrite elements_union_singleton.
    + rewrite <- (IHsz' (S start')) at 2 by lia.
      simpl. repeat f_equal; lia.
    + intro H.
      eapply rangeSet_lookup in H; try lia.
      intuition idtac. revert H0. word_cleanup.
Qed.

Lemma rangeSet_append_one:
  ∀ start sz : u64,
    int.Z start + int.Z sz < 2 ^ 64
    → ∀ i : u64,
      int.Z i < int.Z (word.add start sz)
      → int.Z start ≤ int.Z i
      → {[i]} ∪ rangeSet (int.Z start) (int.Z i - int.Z start) =
        rangeSet (int.Z start) (int.Z i - int.Z start + 1).
Proof.
  intros start sz Hbound i Hibound Hilower_bound.
  replace (int.Z (word.add start sz)) with (int.Z start + int.Z sz) in Hibound by word.
  apply gset_eq; intros.
  rewrite elem_of_union.
  rewrite elem_of_singleton.
  rewrite !rangeSet_lookup; try word.
  destruct (decide (x = i)); subst.
  - split; intros; eauto.
    word.
  - intuition; try word.
    right.
    assert (int.Z x ≠ int.Z i) by (apply not_inj; auto).
    word.
Qed.

Lemma rangeSet_first:
  ∀ start sz,
    sz > 0 ->
    rangeSet start sz = {[U64 start]} ∪ rangeSet (start+1) (sz-1).
Proof.
  rewrite /rangeSet.
  intros.
  rewrite seqZ_cons; first by lia.
  simpl.
  reflexivity.
Qed.
