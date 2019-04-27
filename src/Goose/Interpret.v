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

Notation es := (@Proc.State Go.State).
Notation gs := Go.State.
Notation fs := FS.State.
Notation ds := Data.State.

Module RTerm.
  Inductive t : Type -> Type -> Type -> Type :=
  (* atomic operations *)
  | Reads T : (gs -> T) -> t gs gs T
  | Puts : (fs -> fs) -> t fs fs unit
  | ReadSome T : (gs -> option T) -> t gs gs T
  | ReadNone T : (gs -> option T) -> t gs gs unit
  | AllocPtr ty : Data.ptrRawModel ty -> t Go.State Go.State (goModel.(@Ptr) ty)
  | UpdAllocs ty : Ptr ty -> Data.ptrModel ty -> t Go.State Go.State unit
  | DelAllocs ty : Ptr ty -> t Go.State Go.State unit

  (* sequencing *)
  | Pure T : T -> t gs gs T
  | Ret T : T -> t es es T
  | BindES T1 T2 : t es es T1 -> (T1 -> t es es T2) -> t es es T2
  | AndThenGS T1 T2 : t gs gs T1 -> (T1 -> t gs gs T2) -> t gs gs T2
  | AndThenFS T1 T2 : t fs fs T1 -> (T1 -> t fs fs T2) -> t fs fs T2
  | AndThenDS T1 T2 : t ds ds T1 -> (T1 -> t ds ds T2) -> t ds ds T2

  (* zooms *)
  | CallGS T : t gs gs T -> t es es T
  | ZoomFS T : t fs fs T -> t gs gs T
  | ZoomDS T : t ds ds T -> t fs fs T
  | FstLift A1 A2 B T : t A1 A2 T -> t (A1 * B) (A2 * B) T
  | SndLift A1 A2 B T : t A1 A2 T -> t (B * A1) (B * A2) T

  | Error A B T : t A B T
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

Definition ptrMap := nat.
Definition ptrMap_null : ptrMap := 1.

Fixpoint interpret_ds (T : Type) (r : RTerm.t ds ds T) (X : ds*ptrMap) : Output (ds*ptrMap) T :=
  match r with
  | RTerm.AndThenDS r f =>
    let o := interpret_ds r X in
    match o with
    | Success b t => let r' := f t in let o' := interpret_ds r' b in o'
    | Error => Error
    | NotImpl => NotImpl
    end
  | _ => NotImpl
  end.

Fixpoint interpret_fs (T : Type) (r : RTerm.t fs fs T) (X : fs*ptrMap) : Output (fs*ptrMap) T :=
  match r with
  | RTerm.Puts f => Success (f (fst X), snd X) tt
  | RTerm.AndThenFS r f =>
    let o := interpret_fs r X in
    match o with
    | Success b t => let r' := f t in let o' := interpret_fs r' b in o'
    | Error => Error
    | NotImpl => NotImpl
    end
  | RTerm.ZoomDS r => let (f, pm) := X in
                      let d := FS.heap f in
                      match (interpret_ds r (d, pm)) with
                      | Success (d', pm') t => Success (f <| FS.heap := d' |>, pm') t
                      | Error => Error
                      | NotImpl => NotImpl
                      end
  | _ => NotImpl
  end.

Fixpoint interpret_gs (T : Type) (r : RTerm.t gs gs T) (X : gs*ptrMap) : Output (gs*ptrMap) T :=
  match r with
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
  | RTerm.Pure t => Success X t
  | RTerm.AndThenGS r f =>
      let o := interpret_gs r X in
      match o with
      | Success b t => let r' := f t in let o' := interpret_gs r' b in o'
      | Error => Error
      | NotImpl => NotImpl
      end
  | RTerm.ZoomFS r => let (g, pm) := X in
                      let f := Go.fs g in
                      match (interpret_fs r (f, pm)) with
                      | Success (f', pm') t => Success (g <| Go.fs := f' |>, pm') t
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
  | RTerm.Ret t => Success X t
  | RTerm.CallGS r => let (e, pm) := X in
                    let (thr, g) := e in
                    match (interpret_gs r (g, pm)) with
                    | Success (g', pm') t => Success ((thr, g'), pm') t
                    | Error => Error                                                  
                    | NotImpl => NotImpl                                                  
                    end
  | RTerm.BindES r f =>
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
  | RTerm.Reads f => reads f
  | RTerm.ReadSome f => readSome f
  | RTerm.ReadNone f => readNone f
  | RTerm.Puts f => puts f
  | RTerm.AllocPtr _ prm => _zoom Go.fs (_zoom FS.heap (Data.allocPtr _ prm))
  | RTerm.UpdAllocs p pm => _zoom Go.fs (_zoom FS.heap (Data.updAllocs p pm))
  | RTerm.DelAllocs  p => _zoom Go.fs (_zoom FS.heap (Data.delAllocs p))

  | RTerm.Pure o0 => pure o0
  | RTerm.Ret x => pure x
  | RTerm.BindES r1 f => and_then (rtermDenote r1) (fun x => (rtermDenote (f x)))
  | RTerm.AndThenGS r1 f => and_then (rtermDenote r1) (fun x => (rtermDenote (f x)))
  | RTerm.AndThenFS r1 f => and_then (rtermDenote r1) (fun x => (rtermDenote (f x)))
  | RTerm.AndThenDS r1 f => and_then (rtermDenote r1) (fun x => (rtermDenote (f x)))

  | RTerm.CallGS r => snd_lift (rtermDenote r)
  | RTerm.ZoomFS r => _zoom Go.fs (rtermDenote r)
  | RTerm.ZoomDS r => _zoom FS.heap (rtermDenote r)
  | RTerm.FstLift _ r => fst_lift (rtermDenote r)
  | RTerm.SndLift _ r => snd_lift (rtermDenote r)

  | RTerm.Error _ _ _ => error
  | RTerm.NotImpl r => r
  end.

Check @_zoom.
Check @puts.

Ltac refl' RetB RetT e :=
  match eval simpl in e with
  | fun x : ?T => @reads ?A ?T0 (fun (y: ?A) => (@?f x y)) =>
    constr: (fun x => RTerm.Reads (f x))
  | fun x : ?T => @readSome ?A ?T0 (fun (y: ?A) => (@?f x y)) =>
    constr: (fun x => RTerm.ReadSome (f x))
  | fun x : ?T => @readNone ?A ?T0 (fun (y: ?A) => (@?f x y)) =>
    constr: (fun x => RTerm.ReadNone (f x))
  | fun x : ?T => @puts fs (fun (y: fs) => (@?f x y)) =>
    constr: (fun x => RTerm.Puts (f x))
  | fun x: ?T => @Data.allocPtr ?ty ?prm =>
    constr: (fun x => RTerm.AllocPtr ty prm)
  | fun x: ?T => @Data.updAllocs ?ty ?p ?pm =>
    constr: (fun x => RTerm.UpdAllocs ty p pm)
  | fun x: ?T => @Data.delAllocs ?ty ?p =>
    constr: (fun x => RTerm.DelAllocs ty p)

  | fun x : ?T => @pure gs _ (@?E x) =>
    constr: (fun x => RTerm.Pure gs (E x))
  | fun x : ?T => @pure _ _ (@?E x) =>
    constr: (fun x => RTerm.Ret es (E x))

  | fun x: ?T => @and_then Proc.State Proc.State Proc.State ?T1 ?T2 (@?r1 x) (fun (y: ?T1) => (@?r2 x y)) =>
    let f1 := refl' Proc.State T1 r1 in
    let f2 := refl' Proc.State T2 (fun (p: T * T1) => (r2 (fst p) (snd p))) in
    constr: (fun x => RTerm.BindES (f1 x) (fun y => f2 (x, y)))
  | fun x: ?T => @and_then gs gs gs ?T1 ?T2 (@?r1 x) (fun (y: ?T1) => (@?r2 x y)) =>
    let f1 := refl' gs T1 r1 in
    let f2 := refl' gs T2 (fun (p: T * T1) => (r2 (fst p) (snd p))) in
    constr: (fun x => RTerm.AndThenGS (f1 x) (fun y => f2 (x, y)))
  | fun x: ?T => @and_then fs fs fs ?T1 ?T2 (@?r1 x) (fun (y: ?T1) => (@?r2 x y)) =>
    let f1 := refl' fs T1 r1 in
    let f2 := refl' fs T2 (fun (p: T * T1) => (r2 (fst p) (snd p))) in
    constr: (fun x => RTerm.AndThenFS (f1 x) (fun y => f2 (x, y)))
  | fun x: ?T => @and_then ds ds ds ?T1 ?T2 (@?r1 x) (fun (y: ?T1) => (@?r2 x y)) =>
    let f1 := refl' ds T1 r1 in
    let f2 := refl' ds T2 (fun (p: T * T1) => (r2 (fst p) (snd p))) in
    constr: (fun x => RTerm.AndThenDS (f1 x) (fun y => f2 (x, y)))

  | fun x: ?T => @snd_lift gs gs nat ?T (@?r x) =>
    let f := refl' gs T r in
    constr: (fun x => RTerm.CallGS (f x))
  | (fun x: ?T => @_zoom gs fs Go.fs _ ?T1 (@?r1 x)) =>
    let f := refl' fs T1 r1 in
    constr: (fun x: T => RTerm.ZoomFS (f x))
  | (fun x: ?T => @_zoom fs ds FS.heap _ ?T1 (@?r1 x)) =>
    let f := refl' ds T1 r1 in
    constr: (fun x: T => RTerm.ZoomDS (f x))
(*  | fun x: ?T => @fst_lift ?A1 ?A2 ?B ?T (@?r x) =>
    let f := refl' A2 T r in
    constr: (fun x => RTerm.FstLift (f x))
  | fun x: ?T => @snd_lift ?A1 ?A2 ?B ?T (@?r x) =>
    let f := refl' A2 T r in
    constr: (fun x => RTerm.SndLift (f x))  *)

  | fun x : ?T => @error ?A ?B ?T0 =>
    constr: (fun x => RTerm.Error A B T0)
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
  let t := eval simpl in (Proc.exec_step Go.sem p) in
  refl t.

Ltac reflop_fs o :=
  let t := eval simpl in (Go.step (FilesysOp o)) in
      let t' := eval cbv [set] in t in (* expands puts of sets *)
          refl t'.

Ltac reflop_data o :=
  let t := eval simpl in (Go.step (DataOp o)) in
  refl t.

Ltac reflop_glob o :=
  let t := eval simpl in (Go.step (LockGlobalOp o)) in
  refl t.


Eval cbv [set] in (fun inode : FS.Inode => (puts (set FS.fds <[((), inode, tt).2:= (((), inode, tt).1.2, FS.Read)]>))).

Check (fun inode : FS.Inode => (puts (set FS.fds <[((), inode, tt).2:= (((), inode, tt).1.2, FS.Read)]>))).

Definition reify T (op : Op T)  : RTerm.t gs gs T.
  destruct op.
  - destruct o eqn:?;
    match goal with
    | [ H : o = ?A |- _ ] => let x := reflop_fs A in idtac x; exact x
    end.
  - destruct o eqn:?;
    match goal with
    | [ H : o = ?A |- _ ] => let x := reflop_data A in idtac x; exact x
    end.
  - destruct o eqn:?;
    match goal with
    | [ H : o = ?A |- _ ] => let x := reflop_glob A in idtac x; exact x
    end.
Qed.

Definition reify_proc T (proc : proc Op T)  : RTerm.t es es T.
  destruct proc eqn:?.
  match goal with
  | [ H : proc = ?A |- _ ] => let x := reflproc A in idtac x
  end.
  - Set Printing All.
    let t := eval simpl in (Proc.exec_step Go.sem (Call op)) in
        let k := constr:(fun x: unit => t) in
        let j := match k with

                 | fun x: ?T => @and_then ?A ?B ?C ?T1 ?T2 (@?r1 x) (fun (y: ?T1) => (@?r2 x y)) =>
                   let f1 := refl' B T1 r1 in
                   let f2 := refl' C T2 (fun (p: T * T1) => (r2 (fst p) (snd p))) in
                   constr: (fun x => RTerm.Bind (f1 x) (fun y => f2 (x, y)))
                 end in idtac j.
        let x := refl' es T constr:(fun r :unit => t) in idtac x.
        let x' := (eval cbn beta in (x tt)) in pose x'.
  match goal with
  | [ H : proc = ?A |- _ ] => let x := reflproc A in idtac x
  end.

Definition interpret (T : Type) (r: RTerm.t es es T) : es -> Output es T :=
  fun a => match interpret_es r (a, ptrMap_null) with
           | Success x t => Success (fst x) t
           | Error => Error
           | NotImpl => NotImpl
           end.
  
(* Prove Interpreter *)
Theorem interpret_ok : forall T (r: RTerm.t es es T) (a : es),
    match (interpret r a) with
    | NotImpl => True
    | Error => rtermDenote r a Err
    | Success b t => rtermDenote r a (Val b t)
    end.
Admitted.

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