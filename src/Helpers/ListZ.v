From Coq Require Import ZArith Lia.
From Coq Require Import ssreflect.

From stdpp Require Import base numbers.
From stdpp Require list.

Set Default Goal Selector "!".
Set Default Proof Using "Type".

#[local] Open Scope Z.
#[local] Open Scope general_if_scope.

Create HintDb list.
#[local] Ltac Zify.zify_pre_hook ::= autounfold with list in *.

Module listZ.
Section list.
Context {A: Type} `{!Inhabited A}.

Implicit Types (l: list A) (a x: A) (n i: Z).

#[local] Notation lengthN := (Datatypes.length).

Definition length l: Z := Z.of_nat (lengthN l).

(* hopefully not needed but just in case *)
Lemma length_def l : length l = Z.of_nat (lengthN l).
Proof. reflexivity. Qed.
Lemma length_nat l : Z.to_nat (length l) = lengthN l.
Proof. rewrite /length. lia. Qed.

Lemma length_pos l : 0 ≤ length l.
Proof. rewrite /length. lia. Qed.

Lemma length_nil x : length [] = 0.
Proof. reflexivity. Qed.

Lemma length_singleton x : length [x] = 1.
Proof. reflexivity. Qed.

Lemma app_length l1 l2 : length (l1 ++ l2) = length l1 + length l2.
Proof. rewrite /length. rewrite List.app_length. lia. Qed.

Lemma cons_length x l : length (x :: l) = 1 + length l.
Proof. rewrite /length /=. lia. Qed.

#[global] Instance list_lookup : LookupTotal Z A (list A) :=
  λ n l,
    if decide (0 ≤ n) then nth (Z.to_nat n) l inhabitant
    else inhabitant.

Hint Unfold length : list.

Ltac simpl_decide :=
  repeat first [
      rewrite -> decide_True by lia
    ].

Lemma lookupZ_to_lookup l n :
  0 ≤ n < length l →
  l !! (Z.to_nat n) = Some (l !!! n).
Proof.
  autounfold with list => Hbound.
  rewrite /lookup_total /list_lookup.
  simpl_decide.
  destruct (list.nth_lookup_or_length l (Z.to_nat n) inhabitant); [ congruence | ].
  lia.
Qed.

Lemma lookupZ_eq l n x :
  0 ≤ n →
  l !! Z.to_nat n = Some x →
  l !!! n = x.
Proof.
  intros Hle Hget.
  pose proof (list.lookup_lt_Some _ _ _ Hget).
  rewrite lookupZ_to_lookup in Hget; [ lia | ].
  congruence.
Qed.

Lemma list_eq l1 l2 :
  length l1 = length l2 →
  (∀ i, 0 ≤ i < length l1 → l1 !!! i = l2 !!! i) →
  l1 = l2.
Proof.
  intros Hlen Heq.
  apply list.list_eq => i.
  destruct (decide (Z.of_nat i < length l1)).
  { rewrite /lookup_total /list_lookup in Heq.
    pose proof (Heq (Z.of_nat i) ltac:(lia)).
    rewrite -> !decide_True in H by lia.
    rewrite Nat2Z.id in H.
    destruct (list.nth_lookup_or_length l1 i inhabitant),
      (list.nth_lookup_or_length l2 i inhabitant);
      try lia.
    congruence. }
  rewrite list.lookup_ge_None_2; [ lia | ].
  rewrite list.lookup_ge_None_2; [ lia | ].
  auto.
Qed.

Lemma lookup_oob l i :
  ¬(0 ≤ i < length l) →
  l !!! i = inhabitant.
Proof.
  intros H.
  rewrite /lookup_total /list_lookup.
  destruct (decide _); auto.
  rewrite nth_overflow //; lia.
Qed.

Lemma lookup_lookup_eq l1 l2 i1 i2 :
  (0 ≤ i1 < length l1 ↔ 0 ≤ i2 < length l2) →
  (∀ x y, l1 !! (Z.to_nat i1) = Some x →
          l2 !! (Z.to_nat i2) = Some y →
          x = y) →
  l1 !!! i1 = l2 !!! i2.
Proof.
  intros H12 Heq.
  destruct (decide (0 ≤ i1 < length l1)) as [H1 | H1].
  {
    pose proof H1 as H2. apply H12 in H2.
    assert (is_Some (l1 !! Z.to_nat i1)) as [x Hget1].
    { eapply list.lookup_lt_is_Some_2.
      lia. }
    assert (is_Some (l2 !! Z.to_nat i2)) as [y Hget2].
    { eapply list.lookup_lt_is_Some_2.
      lia. }
    pose proof (Heq x y ltac:(auto) ltac:(auto)); subst.
    erewrite lookupZ_eq; eauto; try lia.
    erewrite lookupZ_eq; eauto; try lia.
  }
  assert (¬(0 ≤ i2 < length l2)) by intuition.
  rewrite lookup_oob; [ lia | ].
  rewrite lookup_oob; [ lia | ].
  auto.
Qed.

Lemma lookup_app_l l1 l2 i :
  i < length l1 →
  (l1 ++ l2) !!! i = l1 !!! i.
Proof.
  intros H.
  destruct (decide (0 ≤ i)).
  2: { rewrite !lookup_oob; auto; try lia. }
  apply lookup_lookup_eq.
  { rewrite app_length. lia. }
  intros ??.
  rewrite list.lookup_app_l; [ lia | ].
  congruence.
Qed.

#[global] Instance list_insert : Insert Z A (list A) :=
  λ n x l, if decide (0 ≤ n) then <[ Z.to_nat n := x ]> l else l.

#[local] Lemma list_insert_nat l n x :
  0 ≤ n →
  <[ n := x ]> l = <[ Z.to_nat n := x ]> l.
Proof.
  intros.
  rewrite {1}/insert /list_insert.
  simpl_decide => //.
Qed.

Lemma list_insert_length n x l :
  length (<[ n := x ]> l) = length l.
Proof.
  rewrite /insert /list_insert.
  destruct (decide _); auto.
  rewrite /length list.insert_length //.
Qed.

Lemma insert_lookup_eq n x l i :
  (0 ≤ n < length l) →
  i = n →
  <[ n := x ]> l !!! n = x.
Proof.
  intros Hbound ->; subst; simpl_decide.
  pose proof (lookupZ_to_lookup l n ltac:(auto)).
  rewrite list_insert_nat; [ lia | ].
  apply lookupZ_eq; [ lia | ].
  rewrite list.list_lookup_insert //.
  lia.
Qed.

Definition drop n l := skipn (Z.to_nat n) l.
Definition take n l := firstn (Z.to_nat n) l.

Lemma drop_length' l n :
  (* the length has to be clamped to [0, length l] *)
  length (drop n l) = (length l - n) `max` 0 `min` length l.
Proof.
  rewrite /length /drop.
  rewrite skipn_length.
  lia.
Qed.

Lemma drop_length l n :
  0 ≤ n < length l →
  length (drop n l) = length l - n.
Proof.
  intros H.
  rewrite drop_length'.
  lia.
Qed.

Lemma lookup_drop l n i :
  (* TODO: generalize to an out-of-bounds case *)
  0 ≤ n ≤ length l →
  0 ≤ i < length l - n →
  drop n l !!! i = l !!! (n + i).
Proof.
  intros H1 H2.
  apply lookup_lookup_eq.
  { rewrite drop_length'; lia. }
  intros ??.
  rewrite list.lookup_drop.
  assert ((Z.to_nat n + Z.to_nat i)%nat = Z.to_nat (n + i)) by lia.
  congruence.
Qed.

Lemma take_length' l n :
  length (take n l) = n `max` 0 `min` length l.
Proof.
  rewrite /length /take.
  rewrite firstn_length.
  lia.
Qed.

Lemma take_length l n :
  0 ≤ n ≤ length l →
  length (take n l) = n.
Proof.
  intros H.
  rewrite take_length'; lia.
Qed.

Lemma lookup_take l n i :
  i < n →
  take n l !!! i = l !!! i.
Proof.
  intros H.
  destruct (decide (0 ≤ i)).
  2: {
    rewrite !lookup_oob; auto; lia.
  }
  apply lookup_lookup_eq.
  { rewrite take_length'; lia. }
  intros ??.
  rewrite list.lookup_take_Some.
  intuition. congruence.
Qed.

Lemma take_nil n :
  take n [] = [].
Proof. rewrite /take firstn_nil //. Qed.

Lemma take_0 l :
  take 0 l = [].
Proof. reflexivity. Qed.
Lemma take_neg l n :
  n ≤ 0 →
  take n l = [].
Proof.
  intros H.
  rewrite /take. replace (Z.to_nat n) with 0%nat by lia. reflexivity.
Qed.

Lemma take_oob l n :
  length l ≤ n →
  take n l = l.
Proof.
  intros H; rewrite /take.
  rewrite firstn_all2 //. lia.
Qed.

Lemma drop_nil n :
  drop n [] = [].
Proof. rewrite /drop skipn_nil //. Qed.

Lemma drop_0 l :
  drop 0 l = l.
Proof. rewrite /drop skipn_O //. Qed.
Lemma drop_neg n l :
  n ≤ 0 →
  drop n l = l.
Proof.
  intros H; rewrite /drop.
  replace (Z.to_nat n) with 0%nat by lia.
  rewrite skipn_O //.
Qed.

Lemma drop_oob l n :
  length l ≤ n →
  drop n l = [].
Proof.
  intros H.
  rewrite /drop.
  rewrite skipn_all2 //. lia.
Qed.

Lemma take_drop i l :
  take i l ++ drop i l = l.
Proof.
  rewrite /take /drop.
  rewrite firstn_skipn //.
Qed.

End list.

Lemma fmap_length {A B} `{!Inhabited A, !Inhabited B}
  (f: A → B) (l: list A) :
  length (f <$> l) = length l.
Proof.
  rewrite /length.
  rewrite list.fmap_length //.
Qed.

Lemma list_lookup_fmap {A B} `{!Inhabited A, !Inhabited B}
  (f: A → B) (l: list A) i :
  0 ≤ i < length l →
  (f <$> l) !!! i = f (l !!! i).
Proof.
  intros Hbound.
  apply lookupZ_eq; [ lia | ].
  rewrite list.list_lookup_fmap.
  assert (is_Some (l !! Z.to_nat i)) as [x Hget].
  { apply list.lookup_lt_is_Some. rewrite /length in Hbound; lia. }
  rewrite Hget /=.
  apply lookupZ_eq in Hget.
  - congruence.
  - lia.
Qed.

End listZ.

Opaque listZ.length.
Opaque listZ.list_lookup.
Opaque listZ.list_insert.
