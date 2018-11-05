From Coq Require Import List.
From Coq Require Import Omega.

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

  Fixpoint sel l n : A :=
    match l with
    | nil => default
    | x::xs => match n with
              | 0 => x
              | S n => sel xs n
              end
    end.

  Theorem sel_assign l : forall n x',
      n < length l ->
      sel (assign l n x') n = x'.
  Proof.
    induct l.
  Qed.

  Theorem sel_assign_ne l : forall n1 n2 x',
      n1 <> n2 ->
      sel (assign l n2 x') n1 = sel l n1.
  Proof.
    induct l.
    - generalize dependent n.
      induction n2; simpl; intros.
      + destruct n; auto; try congruence.
      + destruct n; auto.
  Qed.

End Array.
