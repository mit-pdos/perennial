From Coq Require Import ssreflect.
From stdpp Require Import gmap fin_sets.
From Perennial.Helpers Require Import Integers.

Definition rangeSet (start sz: Z): gset u64 :=
  list_to_set (U64 <$> seqZ start sz).

(* TODO: upstream this *)
Lemma seqZ_app (len1 len2 start: Z) :
  0 ≤ len1 →
  0 ≤ len2 →
  seqZ start (len1 + len2) = seqZ start len1 ++ seqZ (start + len1) len2.
Proof.
  intros.
  rewrite /seqZ //.
  replace (Z.to_nat (len1 + len2)) with (Z.to_nat len1 + Z.to_nat len2)%nat
    by lia.
  rewrite seq_app fmap_app.
  f_equal.
  replace (0 + Z.to_nat len1)%nat with (Z.to_nat len1 + 0)%nat by lia.
  rewrite -fmap_add_seq.
  rewrite -list_fmap_compose.
  apply list_fmap_ext; auto.
  move=> x /=; lia.
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
