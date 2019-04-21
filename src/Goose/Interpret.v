From stdpp Require Import base countable.
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

    Ptr ty := nat;
    nullptr ty := 0;
    }.

Declare Instance goModelWf : GoModelWf goModel.

Definition es : Type := (@Proc.State Go.State).
Definition gs : Type := Go.State.
Definition fs : Type := FS.State.
Definition ds : Type := Data.State.

Module RTerm.
  Inductive t : Type -> Type -> Type -> Type :=
  | Pure A T : T -> t A A T
  (* We won't be able to interpret this without a particular T being
     specified, so we require one in the constructor. *)
  (* | Identity A T : T -> t A A T *)
  (* | None A B T : t A B T *)
  | Reads T : (gs -> T) -> t gs gs T
  | Puts : (gs -> gs) -> t gs gs unit
  | Error A B T : t A B T
  | ReadSome T : (gs -> option T) -> t gs gs T
  | ReadNone T : (gs -> option T) -> t gs gs unit
  | AndThen T1 T2 : t gs gs T1 -> (T1 -> t gs gs T2) -> t gs gs T2
  | AllocPtr ty : Data.ptrRawModel ty -> t Go.State Go.State (goModel.(@Ptr) ty)
  | UpdAllocs ty : Ptr ty -> Data.ptrModel ty -> t Go.State Go.State unit
  | DelAllocs ty : Ptr ty -> t Go.State Go.State unit
  | FstLift A1 A2 B T : t A1 A2 T -> t (A1 * B) (A2 * B) T
  | SndLift A1 A2 B T : t A1 A2 T -> t (B * A1) (B * A2) T
  | NotImpl A B T (r: relation A B T) : t A B T

  | Ret A T : T -> t A A T (* same as Pure, and we could just refl Rets to Pures *)
  | Call T : t gs gs T -> t es es T
  | Bind T1 T2 : t es es T1 -> (T1 -> t es es T2) -> t es es T2 (* Could be AndThens *)
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

Definition ptrMap := nat.
Definition ptrMap_null : ptrMap := 1.

Fixpoint interpret_gs (T : Type) (r : RTerm.t gs gs T) (X : gs*ptrMap) : Output (gs*ptrMap) T :=
  match r with
  | RTerm.Pure A t => Success X t
  | RTerm.Reads f => Success X (f (fst X))
  | RTerm.ReadSome f =>
      let t' := f (fst X) in match t' with
                        | Some t => Success X t
                        | None => Error
                        end
  | RTerm.ReadNone f =>
      let t' := f (fst X) in match t' with
                        | Some t => Error
                        | None => Success X tt
                        end
  | RTerm.Puts f => Success (f (fst X), snd X) tt
  | RTerm.Error _ _ _ => (Error)
  | RTerm.AllocPtr _ prm => 
    let p := snd X
                 in let f := (set Go.fs (set FS.heap (@set Data.State (DynMap goModel.(@Ptr) Data.ptrModel) Data.allocs _ (updDyn p (Unlocked, prm)))))
                        in Success (f (fst X), (snd X) + 1) p
  | RTerm.UpdAllocs p pm =>
    let f := (set Go.fs (set FS.heap (@set Data.State _ Data.allocs _ (updDyn p pm))))
                        in Success (f (fst X), snd X) tt
  | RTerm.DelAllocs p =>
    let f := (set Go.fs (set FS.heap (@set Data.State _ Data.allocs _ (deleteDyn p))))
                        in Success (f (fst X), snd X) tt
  | RTerm.AndThen r f =>
      let o := interpret_gs r X in
      match o with
      | Success b t => let r' := f t in let o' := interpret_gs r' b in o'
      | Error => Error
      | NotImpl => NotImpl
      end
  | RTerm.FstLift _ _ => NotImpl
  | RTerm.SndLift _ _ => NotImpl
  | RTerm.NotImpl _ => NotImpl
  | _ => NotImpl
  end.

Fixpoint interpret_es (T : Type) (r : RTerm.t es es T) (X : es*ptrMap) : Output (es*ptrMap) T :=
  match r with
  | RTerm.Ret A t => Success X t
  | RTerm.Call r => let (e, pm) := X in
                    let (thr, g) := e in
                    match (interpret_gs r (g, pm)) with
                    | Success (g', pm') t => Success ((thr, g'), pm') t
                    | Error => Error                                                  
                    | NotImpl => NotImpl                                                  
                    end
  | RTerm.Bind r f =>
      let o := interpret_es r X in
      match o with
      | Success e t => let r' := f t in let o' := interpret_es r' e in o'
      | Error => Error
      | NotImpl => NotImpl
      end
  | _ => NotImpl
  end.

Fixpoint rtermDenote A B T (r: RTerm.t A B T) : relation A B T :=
  match r with
  | RTerm.Pure _ o0 => pure o0
  | RTerm.Reads f => reads f
  | RTerm.ReadSome f => readSome f
  | RTerm.ReadNone f => readNone f
  | RTerm.Puts f => puts f
  | RTerm.Error _ _ _ => error
  | RTerm.AllocPtr _ prm => _zoom Go.fs (_zoom FS.heap (Data.allocPtr _ prm))
  | RTerm.UpdAllocs p pm => _zoom Go.fs (_zoom FS.heap (Data.updAllocs p pm))
  | RTerm.DelAllocs  p => _zoom Go.fs (_zoom FS.heap (Data.delAllocs p))
  | RTerm.AndThen r1 f => and_then (rtermDenote r1) (fun x => (rtermDenote (f x)))
  | RTerm.FstLift _ r => fst_lift (rtermDenote r)
  | RTerm.SndLift _ r => snd_lift (rtermDenote r)
  | RTerm.NotImpl r => r
                         
  | RTerm.Ret _ x => pure x
  | RTerm.Bind r1 f => and_then (rtermDenote r1) (fun x => (rtermDenote (f x)))
  | RTerm.Call r => snd_lift (rtermDenote r)
  end.

Ltac refl' RetB RetT e :=
  match eval simpl in e with
  | fun x : ?T => @pure gs _ (@?E x) =>
    constr: (fun x => RTerm.Pure gs (E x))

  | fun x : ?T => @pure es _ (@?E x) =>
    constr: (fun x => RTerm.Ret es (E x))

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

  | fun x: ?T => @Data.allocPtr ?ty ?prm =>
    constr: (fun x => RTerm.AllocPtr ty prm)

  | fun x: ?T => @Data.updAllocs ?ty ?p ?pm =>
    constr: (fun x => RTerm.UpdAllocs ty p pm)

  | fun x: ?T => @Data.delAllocs ?ty ?p =>
    constr: (fun x => RTerm.DelAllocs ty p)

  | fun x: ?T => @and_then gs gs gs ?T1 ?T2 (@?r1 x) (fun (y: ?T1) => (@?r2 x y)) =>
    let f1 := refl' gs T1 r1 in
    let f2 := refl' gs T2 (fun (p: T * T1) => (r2 (fst p) (snd p))) in
    constr: (fun x => RTerm.AndThen (f1 x) (fun y => f2 (x, y)))

  | fun x: ?T => @and_then es es es ?T1 ?T2 (@?r1 x) (fun (y: ?T1) => (@?r2 x y)) =>
    let f1 := refl' es T1 r1 in
    let f2 := refl' es T2 (fun (p: T * T1) => (r2 (fst p) (snd p))) in
    constr: (fun x => RTerm.Bind (f1 x) (fun y => f2 (x, y)))

  | fun x: ?T => @fst_lift ?A1 ?A2 ?B ?T (@?r x) =>
    let f := refl' A2 T r in
    constr: (fun x => RTerm.FstLift (f x))

  | fun x: ?T => @snd_lift gs gs nat ?T (@?r x) =>
    let f := refl' gs T r in
    constr: (fun x => RTerm.Call (f x))
              
(*  | fun x: ?T => @snd_lift ?A1 ?A2 ?B ?T (@?r x) =>
    let f := refl' A2 T r in
    constr: (fun x => RTerm.SndLift (f x))*)

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

Ltac reflproc p :=
  let t := eval cbv [Proc.exec_step] in (Proc.exec_step Go.sem p) in
  refl t.

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

Definition reify_proc T {model : GoModel} {model_wf : GoModelWf model}
           (proc : proc Op T)  : RTerm.t es es T.
  destruct proc eqn:?;
  match goal with
  | [ H : proc = ?A |- _ ] => let x := reflproc A in idtac x
  end.


(* Prove Interpreter *)
Theorem interpret_ok : forall A B T (r: RTerm.t A B T) (a : A),
    match (interpret r a) with
    | NotImpl => True
    | Error => rtermDenote r a Err
    | Success b t => rtermDenote r a (Val b t)
    end.
Proof.
  intros.
  pose (interpret r a).
  inversion o.
  - admit.

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