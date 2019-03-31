From RecoveryRefinement Require Import Spec.SemanticsHelpers.

From stdpp Require Import base.
From Tactical Require Import ProofAutomation.

From RecoveryRefinement Require Import Helpers.RelationAlgebra.
From RecordUpdate Require Import RecordSet.
From RecoveryRefinement Require Import Helpers.RecordZoom.

From RecoveryRefinement Require Import Spec.Proc.
From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement Require Import Spec.Layer.
From RecoveryRefinement Require Import Goose.Filesys Goose.Heap Goose.GoLayer.

Module RTerm.
Inductive t : Type -> Type -> Type -> Type :=
| Pure A T : T -> t A A T
(* | Identity A T : t A A T *)
(* | None A B T : t A B T *)
| Reads A T : (A -> T) -> t A A T
| Puts A : (A -> A) -> t A A unit
| Error A B T : t A B T
| ReadSome A T : (A -> option T) -> t A A T
| ReadNone A T : (A -> option T) -> t A A unit
| AndThen A B C T1 T2 : t A B T1 -> (T1 -> t B C T2) -> t A C T2
(* | SuchThat A T : (A -> T -> Prop) -> t A A T *)
| NotImpl A B T (r: relation A B T) : t A B T
.
End RTerm.

Inductive Output B T : Type :=
| Success (b: B) (t: T) 
| Error
| NotImpl
.

Arguments Success {_ _}.
Arguments Error {_ _}.
Arguments NotImpl {_ _}.

Fixpoint interpret (A B T : Type) (r : RTerm.t A B T) (X : A) : Output B T :=
  match r in (RTerm.t A B T) return (A -> Output B T) with
  | RTerm.Pure A t => fun a => Success a t
  | RTerm.Reads f => fun a => Success a (f a)
  | RTerm.ReadSome f =>
      fun a =>
      let t' := f a in match t' with
                        | Some t => Success a t
                        | None => Error
                        end
  | RTerm.ReadNone f =>
      fun a =>
      let t' := f a in match t' with
                        | Some t => Error
                        | None => Success a tt
                        end
  | RTerm.Puts f => fun a => Success (f a) tt
  | RTerm.Error _ _ _ => fun a => Error
  | RTerm.AndThen r f =>
      fun a =>
      let o := interpret r a in
      match o with
      | Success b t => let r' := f t in let o' := interpret r' b in o'
      | Error => Error
      | NotImpl => NotImpl
      end
  | RTerm.NotImpl _ => fun a => NotImpl
  end X. 

Fixpoint rtermDenote A B T (r: RTerm.t A B T) : relation A B T :=
  match r with
  | RTerm.Pure _ o0 => pure o0
  | RTerm.Reads f => reads f
  | RTerm.ReadSome f => readSome f
  | RTerm.ReadNone f => readNone f
  | RTerm.Puts f => puts f
  | RTerm.Error _ _ _ => error
  | RTerm.AndThen r1 f => and_then (rtermDenote r1) (fun x => (rtermDenote (f x)))
  | RTerm.NotImpl r => r
  end.

Ltac refl' RetB RetT e :=
  match eval simpl in e with
  | fun x : ?T => @pure ?A _ (@?E x) =>
    constr: (fun x => RTerm.Pure A (E x))

  | fun x : ?T => @reads ?A ?T0 (fun (y: ?A) => (@?f x y)) =>
    constr: (fun x => RTerm.Reads (f x))
              
  | fun x : ?T => @readSome ?A ?T0 (fun (y: ?A) => (@?f x y)) =>
    constr: (fun x => RTerm.ReadSome (f x))

  | fun x : ?T => @readNone ?A ?T0 (fun (y: ?A) => (@?f x y)) =>
    constr: (fun x => RTerm.ReadNone (f x))

  | fun x : ?T => @puts ?A ?A (fun (y: ?A) => (@?f x y)) =>
    constr: (fun x => RTerm.Puts (f x))

  | fun x : ?T => @error ?A ?B ?T0 =>
    constr: (fun x => RTerm.Error A B T0)

  | fun x: ?T => @and_then ?A ?B ?C ?T1 ?T2 (@?r1 x) (fun (y: ?T1) => (@?r2 x y)) =>
    let f1 := refl' B T1 r1 in
    let f2 := refl' C T2 (fun (p: T * T1) => (r2 (fst p) (snd p))) in
    constr: (fun x => RTerm.AndThen (f1 x) (fun y => f2 (x, y)))
              
  | fun x : ?T => @?E x =>
    constr: (fun x => RTerm.NotImpl (E x))
  end.

Ltac refl e :=
  lazymatch type of e with
  | @relation _ ?B ?T =>                        
    let t := refl' B T constr:(fun _ : unit => e) in
    let t' := (eval cbn beta in (t tt)) in
    constr:(t')
  end.

Ltac test e :=
  let t := refl e in
  let e' := eval cbv [rtermDenote] in (rtermDenote t) in
  unify e e'.

Ltac reflop_fs o :=
  let t := eval cbv [FS.step] in (FS.step o) in
  refl t.

Ltac reflop_data o :=
  let t := eval simpl in (_zoom FS.heap (Data.step o)) in
  refl t.

Definition reify T {model : Machine.GoModel} {model_wf : Machine.GoModelWf model}
           (op : Op T)  : RTerm.t FS.State FS.State T.
  destruct op.
  - destruct o eqn:?;
    match goal with
    | [ H : o = ?A |- _ ] => let x := reflop_fs A in exact x
    end.
  - destruct o eqn:?;
    match goal with
    | [ H : o = ?A |- _ ] => let x := reflop_data A in exact x
    end.
Qed.

(* Tests *)    
Ltac testPure := test (pure (A:=unit) 1).
Ltac testReads := test (reads (A:=nat) (fun x : nat => x + 3)).                         
Ltac testReadSome := test (and_then (pure 3) (fun x : nat => readSome (A:=nat) (T:=nat) (fun x0 : nat => Some (x0 + x)))).
Ltac testReadNone := test (and_then (pure 3) (fun x : nat => readNone (A:=nat) (T:=nat) (fun x0 : nat => Some (x0 + x)))).
Ltac testAndThen := test (and_then (pure 3) (fun _: nat => pure (A:=nat) 1)).

Definition ex1 : RTerm.t nat nat nat :=
  RTerm.AndThen (RTerm.Pure nat 3) (fun n => RTerm.ReadSome (fun x => Some (x+n))).
Definition ex2 : RTerm.t nat nat nat :=
  RTerm.AndThen (RTerm.Pure nat 3) (fun n => RTerm.Reads (fun x => (x+n))).
Definition ex3 : RTerm.t nat nat nat :=
  RTerm.AndThen (RTerm.ReadSome (fun x => Some (x+1))) (fun n => RTerm.Reads (fun x => (x+n))).
Definition ex4 : RTerm.t nat nat unit :=
  RTerm.AndThen (RTerm.Pure nat 3) (fun n => RTerm.Puts (fun x => x+n)).

Goal False.
  testPure.
  testReads.
  testReadSome.
  testReadNone.
  testAndThen.
  test (puts (fun x : nat => 3)).
  test (puts (fun x : unit => tt)).
  test (error: relation nat nat nat).
  test (rtermDenote ex1).
  test (rtermDenote ex2).
  test (rtermDenote ex3).
  test (rtermDenote ex4).
Abort.

Compute (interpret ex1 7).
Compute (interpret ex2 7).
Compute (interpret ex3 7).
Compute (interpret ex4 7).
Compute (interpret (RTerm.Error nat nat nat)).