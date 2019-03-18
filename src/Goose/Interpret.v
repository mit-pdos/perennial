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

Ltac refl' e :=
  match eval simpl in e with
  | fun x : ?T => @pure ?A _ (@?E x) =>
    constr:(fun x => Pure A (E x))

  | fun x : ?T => @reads ?A ?T0 (fun (y: ?A) => (@?f x y)) =>
    constr: (fun x => Reads (f x))
              
  | fun x : ?T => @readSome ?A ?T0 (fun (y: ?A) => (@?f x y)) =>
    constr: (fun x => ReadSome (f x))

  | fun x: ?T => @and_then ?A ?B ?C ?T1 ?T2 (@?r1 x) (fun (y: ?T1) => (@?r2 x y)) =>
    let f1 := refl' r1 in
    let f2 := refl' (fun (p: T * T1) => (r2 (fst p) (snd p))) in
    constr: (fun x => AndThen (f1 x) (fun y => f2 (x, y)))
              
  end.

Ltac test e :=
  let e' := refl' constr:(fun _ : unit => e) in
  let e'' := eval cbv [rtermDenote] in (rtermDenote (e' tt)) in
  unify e e''.

Ltac testPure := test (pure (A:=unit) 1).
Ltac testReads := test (reads (A:=nat) (fun x : nat => x + 3)).
Ltac testReadSome := test (and_then (pure 3) (fun x : nat => readSome (A:=nat) (T:=nat) (fun x0 : nat => Some (x0 + x)))).
Ltac testAndThen := test (and_then (pure 3) (fun _: nat => pure (A:=nat) 1)).

Definition ex1 : rterm nat nat nat := AndThen (Pure nat 3) (fun n => ReadSome (fun x => Some (x+n))).
Definition ex2 : rterm nat nat nat := AndThen (Pure nat 3) (fun n => Reads (fun x => (x+n))).
Definition ex3 : rterm nat nat nat := AndThen (ReadSome (fun x => Some (x+1))) (fun n => Reads (fun x => (x+n))).
Eval cbv [rtermDenote ex1] in (rtermDenote ex1).

Goal False.
  testPure.
  testReads.
  testReadSome.
  testAndThen.
  test (rtermDenote ex1).
  test (rtermDenote ex2).
  test (rtermDenote ex3).
Abort.
