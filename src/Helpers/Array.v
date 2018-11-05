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
    induction l; simpl; intros n **;
    [ eauto; try omega | destruct n; simpl in *; eauto; try omega ].

  Theorem assign_length l x' : forall n,
    length (assign l n x') = length l.
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

End Array.
