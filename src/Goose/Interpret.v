(* Why does leaving out this import change implicit argument recognition for Pure? *)
From RecoveryRefinement Require Import Spec.SemanticsHelpers.
From RecoveryRefinement Require Import Helpers.RelationAlgebra.

(* Do we need a rtype and rtypeDenote? *)
Inductive rterm : Type -> Type -> Type -> Type :=
| Pure : forall A T, T -> rterm A A T
| Reads : forall A T, (A -> T) -> rterm A A T
| ReadSome : forall A T, (A -> option T) -> rterm A A T
| AndThen : forall A B C T1 T2,
    rterm A B T1 -> (T1 -> rterm B C T2) -> rterm A C T2
.

Fixpoint rtermDenote A B T (r: rterm A B T) : relation A B T :=
  match r with
  | Pure _ o0 => pure o0
  | Reads f => reads f
  | ReadSome f => readSome f
  | AndThen r1 f => and_then (rtermDenote r1) (fun x => (rtermDenote (f x)))
  end.

Definition ex : rterm nat nat nat := AndThen (Pure nat 3) (fun n => Reads (fun x => x+n)).

Print ex.
Type ex.
Compute (rtermDenote ex).