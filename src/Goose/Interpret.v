From RecoveryRefinement Require Import Spec.SemanticsHelpers.

From stdpp Require Import base.
From Tactical Require Import ProofAutomation.

From RecoveryRefinement Require Import Helpers.RelationAlgebra.

From RecoveryRefinement Require Import Spec.Proc.
From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement Require Import Spec.Layer.
From RecoveryRefinement Require Export Filesys.

Inductive rterm : Type -> Type -> Type -> Type :=
| Pure A T : T -> rterm A A T
(* | Identity A T : rterm A A T *)
(* | Any A B T : rterm A B T *)
(* | None A B T : rterm A B T *)
| Reads A T : (A -> T) -> rterm A A T
(* | Puts A unit : (A -> A) -> rterm A A unit *)
(* | Error A B T : rterm A B T *)
| ReadSome A T : (A -> option T) -> rterm A A T
(* | ReadNone A T : (A -> option T) -> rterm A A unit *)
| AndThen A B C T1 T2 : rterm A B T1 -> (T1 -> rterm B C T2) -> rterm A C T2
(* | SuchThat A T : (A -> T -> Prop) -> rterm A A T *)
.

Inductive Output B T : Type :=
| Success (b: B) (t: T) 
| Error
| NotImpl
.

Arguments Success {_ _}.
Arguments Error {_ _}.
Arguments NotImpl {_ _}.

Fixpoint interpret (A B T : Type) (r : rterm A B T) (X : A) : Output B T :=
  match r in (rterm A B T) return (A -> Output B T) with
  | Pure A t => fun a => Success a t
  | Reads f => fun a => Success a (f a)
  | ReadSome f =>
      fun a =>
      let t' := f a in match t' with
                        | Some t => Success a t
                        | None => Error
                        end
  | AndThen r f =>
      fun a =>
      let o := interpret r a in
      match o with
      | Success b t => let r' := f t in let o' := interpret r' b in o'
      | Error => Error
      | NotImpl => NotImpl
      end
  end X. 

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
              
  | _ => ltac:(idtac e)
  end.

Ltac refl e :=
  let t := refl' constr:(fun _ : unit => e) in
  let t' := (eval cbn beta in (t tt)) in
  constr:(t').

Ltac test e :=
  let t := refl e in
  let e' := eval cbv [rtermDenote] in (rtermDenote t) in
  unify e e'.

Ltac refl_op o :=
  let t := eval cbv [FS.step] in (FS.step o) in
  refl t.

Definition reify A B T (op : FS.Op A) : rterm A B T.
  destruct op eqn:?.
  - let x := reflop (FS.Open p) in idtac x.
    pose proof (FS.step) as step.

(* Tests *)    
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

Compute (interpret ex1 7).
Compute (interpret ex2 7).
Compute (interpret ex3 7).