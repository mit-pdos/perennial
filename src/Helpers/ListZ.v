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

Lemma lookup_oob l i :
  ¬(0 ≤ i < length l) →
  l !!! i = inhabitant.
Proof.
  intros H.
  rewrite /lookup_total /list_lookup.
  destruct (decide _); auto.
  rewrite nth_overflow //; lia.
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
  0 ≤ n →
  length (drop n l) = (length l - n) `max` 0.
Proof.
  rewrite /length /drop => H.
  rewrite skipn_length.
  lia.
Qed.

Lemma drop_length l n :
  0 ≤ n < length l →
  length (drop n l) = length l - n.
Proof.
  intros H.
  rewrite drop_length'; [ lia | ].
  lia.
Qed.

Lemma lookup_drop l n i :
  (* TODO: generalize to an out-of-bounds case *)
  0 ≤ n < length l →
  0 ≤ i < length l - n →
  drop n l !!! i = l !!! (n + i).
Proof.
  intros H1 H2.
  apply lookupZ_eq; [ lia | ].
  rewrite list.lookup_drop.
  rewrite list.list_lookup_lookup_total_lt; [ lia | ].
  f_equal.
  symmetry; apply lookupZ_eq; [ lia | ].
  rewrite list.list_lookup_lookup_total_lt; [ lia | ].
  do 2 f_equal; lia.
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
  assert (exists x, l !! Z.to_nat i = Some x) as [x Hget].
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
