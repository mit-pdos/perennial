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

(* just for illustration *)
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
Admitted.


End listZ.

Opaque listZ.length.
Opaque listZ.list_lookup.
Opaque listZ.list_insert.
