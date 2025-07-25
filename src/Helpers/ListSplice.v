From stdpp Require Import list.
From Coq Require Import ssreflect.

From Perennial.Helpers Require Import ListLen.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Section list.

Context {A: Type}.
Implicit Types (l: list A) (x a: A) (n: nat).

(* list_splice is intended to be used with [n + length l' ≤ l], so that [l']
replaces elements of l.  *)
Definition list_splice l n l' :=
  take n l ++
    (* we truncate l' so that the result is always the length of l without a
side condition; [list_splice_in_bounds] shows an equivalence to a simpler
definition that always inserts all of l'
     *)
    (take (Nat.min (length l') (length l - n)) l') ++
    drop (n + length l') l.

Lemma list_splice_length l n l' :
  length (list_splice l n l') = length l.
Proof.
  rewrite /list_splice.
  len.
Qed.

Lemma lookup_list_splice_old l n l' i :
  ¬(n ≤ i < n + length l') →
  list_splice l n l' !! i = l !! i.
Proof.
  intros.
  rewrite /list_splice.
  destruct (decide (i < length l)).
  - destruct (decide (i < n)).
    + rewrite lookup_app_l; len.
      rewrite lookup_take_lt //.
    + rewrite lookup_app_r; len.
      rewrite lookup_app_r; len.
      rewrite lookup_drop //.
      f_equal.
      lia.
  - rewrite !lookup_ge_None_2 //; len.
Qed.

Lemma lookup_list_splice_new l n l' i :
  n + length l' ≤ length l →
  n ≤ i < n + length l' →
  list_splice l n l' !! i = l' !! (i - n).
Proof.
  intros.
  rewrite /list_splice.
  rewrite lookup_app_r; len.
  rewrite lookup_app_l; len.
  rewrite lookup_take_lt; len.
  f_equal; lia.
Qed.

Lemma lookup_list_Some l n l' i x :
  n + length l' ≤ length l →
  list_splice l n l' !! i = Some x →
  (n ≤ i < n + length l' ∧ l' !! (i - n) = Some x) ∨
  ((i < n ∨ i ≥ n + length l') ∧ l !! i = Some x).
Proof.
  intros Hin_bounds.
  destruct (decide (n ≤ i < n + length l')).
  - rewrite lookup_list_splice_new //.
    eauto.
  - rewrite lookup_list_splice_old //.
    intros.
    right; split; auto. lia.
Qed.

Lemma list_splice_in_bounds l n l' :
  n + length l' ≤ length l →
  list_splice l n l' = take n l ++ l' ++ drop (n + length l') l.
Proof.
  intros.
  rewrite /list_splice.
  rewrite -> Nat.min_l by lia.
  rewrite (take_ge l') //.
Qed.

End list.

Hint Rewrite @list_splice_length using len : len.
