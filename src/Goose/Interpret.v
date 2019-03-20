From RecoveryRefinement Require Import Spec.SemanticsHelpers.
From RecoveryRefinement Require Import Helpers.RelationAlgebra.

Inductive rterm : Type -> Type -> Type -> Type :=
| Pure A T : T -> rterm A A T
| Reads A T : (A -> T) -> rterm A A T
| ReadSome A T : (A -> option T) -> rterm A A T
| AndThen A B C T1 T2 : rterm A B T1 -> (T1 -> rterm B C T2) -> rterm A C T2
.

Inductive Output {B} {T} : Type :=
| Success (s: B) (v: T) 
| Error
.

Arguments Success: clear implicits.

Fixpoint interpret (A B T : Type) (r : rterm A B T) (X : A) : Output :=
  match r in (rterm T0 T1 T2) return (T0 -> Output) with
  | @Pure A0 T0 t => fun X0 : A0 => Success A0 T0 X0 t
  | @Reads A0 T0 t => fun X0 : A0 => Success A0 T0 X0 (t X0)
  | @ReadSome A0 T0 o =>
      fun X0 : A0 =>
      let X1 := o X0 in match X1 with
                        | Some t => Success A0 T0 X0 t
                        | None => Error
                        end
  | @AndThen A0 B0 C T1 T2 r0 r1 =>
      fun X0 : A0 =>
      let X1 := @interpret A0 B0 T1 r0 X0 in
      match X1 with
      | Success _ _ s v => let X2 := r1 v in let X3 := @interpret B0 C T2 X2 s in X3
      | Error => Error
      end
  end X. 

(*
  intros.
  destruct r.
  - exact (Success A T X t).
  - exact (Success A T X (t X)).
  - pose proof (o X).
    destruct X0.
    exact (Success A T X t).
    exact Error.
  - pose proof (interpret A B T1 r X).
    destruct X0.
    + pose proof (r0 v).
      pose proof (interpret B C T2 X0 s).
      exact X1.
    + exact Error.
Qed.
Print interpret.    
*)

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
  let t := refl' constr:(fun _ : unit => e) in
  let t' := (eval cbn beta in (t tt)) in
  constr:(t').

Ltac test e :=
  let t := refl e in
  let e' := eval cbv [rtermDenote] in (rtermDenote t) in
  unify e e'.

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

(* These appear to do the right thing, based on my understanding. I'll
try to get some real examples written soon. *)
Compute (interpret ex1 7).
Compute (interpret ex2 7).
Compute (interpret ex3 7).
