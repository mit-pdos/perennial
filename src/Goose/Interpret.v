From stdpp Require Import base.
From Tactical Require Import ProofAutomation.

From RecordUpdate Require Import RecordSet RecordUpdate.

From RecoveryRefinement Require Import Helpers.RelationAlgebra.
From RecoveryRefinement Require Import Helpers.RecordZoom.
From RecoveryRefinement Require Import Spec.Proc.
From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement Require Import Spec.SemanticsHelpers.
From RecoveryRefinement Require Import Spec.LockDefs.
From RecoveryRefinement Require Import Spec.Layer.
From RecoveryRefinement Require Import Goose.Machine Goose.Filesys Goose.Heap Goose.GoZeroValues Goose.GoLayer Goose.Globals.

Import ProcNotations.

Module RTerm.
  Section GoModel.
  Context `{model_wf : GoModelWf}.
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
  (* | SuchAlloc (ty : Ptr.ty) : t Go.State Go.State (Ptr ty) *)
  | UpdAllocs ty : Ptr ty -> Data.ptrModel ty -> t Go.State Go.State unit
  | DelAllocs ty : Ptr ty -> t Go.State Go.State unit
  | NotImpl A B T (r: relation A B T) : t A B T
  .
  End GoModel.
End RTerm.

Inductive Output B T : Type :=
| Success (b: B) (t: T) 
| Error
| NotImpl
.

Arguments Success {_ _}.
Arguments Error {_ _}.
Arguments NotImpl {_ _}.

Definition ptrMap := unit.
Definition ptrMap_null : ptrMap := tt.

Instance goModel : GoModel :=
  { byte := unit;
    byte0 := tt;

    uint64_to_string n := ""%string;
    ascii_to_byte a := tt;
    byte_to_ascii b := Ascii.zero;

    uint64_to_le u := [tt];
    uint64_from_le bs := None;

    File := unit;
    nilFile := tt;

    Ptr ty := unit;
    nullptr ty := tt;
    }.

Check (set Go.fs).
Check (set FS.heap).
Check (set Data.allocs).
Check (fun x => (set Go.fs (set FS.heap (set Data.allocs x)))).
Check @set.
Check (@set _ _ Data.allocs).
Check (@set Data.State (DynMap goModel.(@Ptr) Data.ptrModel) Data.allocs _).

Fixpoint interpret' (A B T : Type) {model: GoModel} {model_wf: GoModelWf model} (r : RTerm.t A B T) (X : A*ptrMap) : Output (B*ptrMap) T :=
  match r in (RTerm.t A B T) return ((A * ptrMap) -> Output (B * ptrMap) T) with
  | RTerm.Pure A t => fun x => Success x t
  | RTerm.Reads f => fun x => Success x (f (fst x))
  | RTerm.ReadSome f =>
      fun x =>
      let t' := f (fst x) in match t' with
                        | Some t => Success x t
                        | None => Error
                        end
  | RTerm.ReadNone f =>
      fun x =>
      let t' := f (fst x) in match t' with
                        | Some t => Error
                        | None => Success x tt
                        end
  | RTerm.Puts f => fun x => Success (f (fst x), snd x) tt
  | RTerm.Error _ _ _ => (fun x => Error)
  (* Need a way of composing Setters in order to make this better? *)
  | RTerm.UpdAllocs p pm =>
    fun x => let f := (set Go.fs (set FS.heap (@set Data.State (DynMap model.(@Ptr) Data.ptrModel) Data.allocs _ (updDyn p pm))))
                        in Success (f (fst x), snd x) tt
  | RTerm.DelAllocs _ p =>
    fun x => let f := (set Go.fs (set FS.heap (@set Data.State (DynMap model.(@Ptr) Data.ptrModel) Data.allocs _ (deleteDyn p))))
                        in Success (f (fst x), snd x) tt
  | RTerm.AndThen r f =>
      fun x =>
      let o := interpret' r x in
      match o with
      | Success b t => let r' := f t in let o' := interpret' r' b in o'
      | Error => Error
      | NotImpl => NotImpl
      end
  | RTerm.NotImpl _ => (fun x => NotImpl)
  end X.

Definition interpret (A B T : Type) (model: GoModel) (r: RTerm.t A B T) : A -> Return B T :=
  fun a => match interpret' r (a, ptrMap_null) with
           | Success x t => Val (fst x) t
           | Error => Err
           | NotImpl => Err
           end.

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
  let t := eval cbv [FS.step] in (_zoom Go.fs (FS.step o)) in
  refl t.

Ltac reflop_data o :=
  let t := eval simpl in (_zoom Go.fs (_zoom FS.heap (Data.step o))) in
  refl t.

Ltac reflop_glob o :=
  let t := eval simpl in (_zoom Go.maillocks (Globals.step o)) in
  refl t.

Definition reify T {model : GoModel} {model_wf : GoModelWf model}
           (op : Op T)  : RTerm.t Go.State Go.State T.
  destruct op.
  - destruct o eqn:?;
    match goal with
    | [ H : o = ?A |- _ ] => let x := reflop_fs A in exact x
    end.
  - destruct o eqn:?;
    match goal with
    | [ H : o = ?A |- _ ] => let x := reflop_data A in exact x
    end.
  - destruct o eqn:?;
    match goal with
    | [ H : o = ?A |- _ ] => let x := reflop_glob A in exact x
    end.
Qed.

(* Prove Interpreter *)
Theorem interpret_ok : forall A B T (r: RTerm.t A B T) (a : A), (rtermDenote r) a (interpret model r a).

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

Compute (interpret goModel ex1 7).
Compute (interpret ex2 7).
Compute (interpret ex3 7).
Compute (interpret ex4 7).
Compute (interpret (RTerm.Error nat nat nat)).