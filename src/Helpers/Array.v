From Coq Require Import List.
From Coq Require Import Omega.
Require Nat.

Require Import Helpers.Instances.

Set Implicit Arguments.

(* TODO: finish this up and make it an external library *)

Section Array.
  Context (A:Type).
  Context {def: Default A}.
  Notation list := (list A).
  Implicit Types (l:list) (n:nat) (x:A).

  Fixpoint assign l n x' : list :=
    match l with
    | nil => nil
    | x::xs => match n with
              | 0 => x'::xs
              | S n => x::assign xs n x'
              end
    end.

  Hint Extern 3 (_ < _) => omega.

  Ltac induct l :=
    induction l; simpl;
    (intros n **);
     [ eauto; try omega |
       try (destruct n; simpl in *;
            [ eauto; omega | eauto; try omega ]) ].

  Theorem length_assign l x' : forall n,
    length (assign l n x') = length l.
  Proof.
    induct l.
  Qed.

  Theorem assign_oob l x : forall n,
      n >= length l ->
      assign l n x = l.
  Proof.
    induct l.
    rewrite IHl by omega; auto.
  Qed.

  Theorem assign_assign_eq l x1 x2 : forall n,
      assign (assign l n x1) n x2 = assign l n x2.
  Proof.
    induct l.
    rewrite IHl; auto.
  Qed.

  Theorem assign_assign_ne l x1 x2 : forall n1 n2,
      n1 <> n2 ->
      assign (assign l n1 x1) n2 x2 = assign (assign l n1 x1) n2 x2.
  Proof.
    induct l.
  Qed.

  Fixpoint index l n : option A :=
    match l with
    | nil => None
    | x::xs => match n with
              | 0 => Some x
              | S n => index xs n
              end
    end.

  Definition sel l n : A :=
    match index l n with
    | Some x => x
    | None => default
    end.

  Theorem index_assign_eq l : forall n x',
      n < length l ->
      index (assign l n x') n = Some x'.
  Proof.
    induct l.
  Qed.

  Theorem index_assign_ne l : forall n1 n2 x',
      n1 <> n2 ->
      index (assign l n2 x') n1 = index l n1.
  Proof.
    induct l.
    - generalize dependent n.
      induction n2; simpl; intros.
      + destruct n; auto; try congruence.
      + destruct n; auto.
  Qed.

  Local Lemma sel_cons_S x xs n :
    sel (x::xs) (S n) = sel xs n.
  Proof.
    unfold sel; simpl; auto.
  Qed.

  Definition subslice l n m : list :=
    firstn m (skipn n l).

  Theorem subslice_len_general l n m :
    length (subslice l n m) = Nat.min m (length l - n).
  Proof.
    unfold subslice.
    rewrite firstn_length.
    rewrite skipn_length.
    auto.
  Qed.

  Theorem subslice_len l n m :
    n + m <= length l ->
    length (subslice l n m) = m.
  Proof.
    unfold subslice; intros.
    rewrite firstn_length_le; auto.
    rewrite skipn_length; omega.
  Qed.

End Array.
