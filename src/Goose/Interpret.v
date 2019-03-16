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

Ltac refl e :=
  let t := refl' constr:(fun _ : unit => e) in idtac t.

(*                                                       
Ltac refl e :=
  let t := refl' constr:(fun _ : unit => e) in
  eval cbv [rtermDenote t] in (rtermDenote (t tt)).
 *)

Ltac reflPure := refl (pure (A:=unit) 1).
Ltac reflReads := refl (reads (A:=nat) (fun x : nat => x + 3)).
Ltac reflReadSome := refl (and_then (pure 3) (fun x : nat => readSome (A:=nat) (T:=nat) (fun x0 : nat => Some (x0 + x)))).
Ltac reflAndThen := refl (and_then (pure 3) (fun _: nat => pure (A:=nat) 1)).

Goal False.
  reflPure.
  reflReads.
  reflReadSome.
  reflAndThen.
Abort.

Definition ex : rterm nat nat nat := AndThen (Pure nat 3) (fun n => ReadSome (fun x => Some (x+n))).
Eval cbv [rtermDenote ex] in (rtermDenote ex).

Definition refl2_out := (fun x : unit => Reads ((fun (_ : unit) (x0 : nat) => x0 + 3) x)). 
Eval cbv [rtermDenote refl2_out] in (rtermDenote (refl2_out tt)).

Definition refl4_out := (fun x : unit => AndThen ((fun H : unit => Pure nat ((fun _ : unit => 3) H)) x) (fun y : nat => (fun p : unit * nat => Pure nat ((fun _ : unit * nat => 1) p)) (x, y))).
Eval cbv [rtermDenote refl4_out] in (rtermDenote (refl4_out tt)).