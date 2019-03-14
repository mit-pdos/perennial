From RecoveryRefinement Require Import Spec.SemanticsHelpers.
From RecoveryRefinement Require Import Helpers.RelationAlgebra.

Inductive rterm : Type -> Type -> Type -> Type :=
| Pure A T : T -> rterm A A T
| Reads A T : (A -> T) -> rterm A A T
| ReadSome A T : (A -> option T) -> rterm A A T
| AndThen A B C T1 T2 : rterm A B T1 -> (T1 -> rterm B C T2) -> rterm A C T2
.

Fixpoint rtermDenote A B T (r: rterm A B T) : relation A B T :=
  match r with
  | Pure _ o0 => pure o0
  | Reads f => reads f
  | ReadSome f => readSome f
  | AndThen r1 f => and_then (rtermDenote r1) (fun x => (rtermDenote (f x)))
  end.

Definition ex : rterm nat nat nat := AndThen (Pure nat 3) (fun n => Reads (fun x => x+n)).
Definition denoted_ex : relation nat nat nat := and_then (pure 3) (fun x : nat => reads (fun x0 : nat => x0 + x)).
Eval cbv [rtermDenote ex] in (rtermDenote ex).

Ltac refl' e :=
  match eval simpl in e with
  | fun x : _ => pure ?A (@?E x) =>
    let r := refl' E in
    constr:(Pure A (r x))

  | _ => e
  end.

(* (pure nat 2 = pure nat 2) => (Pure nat 2 = Pure nat 2) *)
Ltac refl :=
  match goal with
    | [ |- ?E1 = ?E2 ] =>
      let E1' := refl' (fun _ : unit => E1) in
      let E2' := refl' (fun _ : unit => E2) in
      change (rtermDenote (E1' tt) = rtermDenote (E2' tt));
      cbv beta iota delta
  end.

Compute (pure nat 2).
Goal (pure nat 1) = (pure nat 2).
  refl.
Abort.

Goal (fun x : nat => reads (fun x0 : nat => x0 + x)) = (fun x : nat => reads (fun x0 : nat => x0 + x)).
Abort.

Eval cbv [rtermDenote ex] in (rtermDenote ex).
Compute (rtermDenote ex).