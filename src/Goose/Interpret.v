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
From RecoveryRefinement Require Import Goose.Machine Goose.Filesys
     Goose.Heap Goose.GoZeroValues Goose.GoLayer Goose.Globals.

From RecoveryRefinement Require Import Goose.Examples.UnitTests.
From RecoveryRefinement Require Import Goose.base.
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
Notation G := (slice.t LockRef).

Notation es := (@Proc.State Go.State).
Notation gs := Go.State.
Notation fs := FS.State.
Notation ds := Data.State.
Notation gb := (@Globals.State G).

Module RTerm.
  Inductive t : Type -> Type -> Type -> Type :=
  (* atomic operations *)
  | Reads T : (ds -> T) -> t ds ds T
  | Puts : (fs -> fs) -> t fs fs unit
  | ReadSome T : (ds -> option T) -> t ds ds T
  | ReadNone T : (ds -> option T) -> t ds ds unit
  | ReadsGB T : (gb -> T) -> t gb gb T
  | ReadSomeGB T : (gb -> option T) -> t gb gb T

  | AllocPtr ty : Data.ptrRawModel ty -> t ds ds (goModel.(@Ptr) ty)
  | UpdAllocs ty : Ptr ty -> Data.ptrModel ty -> t ds ds unit
  | DelAllocs ty : Ptr ty -> t ds ds unit

  (* sequencing *)
  | Pure A T : T -> t A A T
  | Ret T : T -> t es es T
  | BindES T1 T2 : t es es T1 -> (T1 -> t es es T2) -> t es es T2
  | AndThenGS T1 T2 : t gs gs T1 -> (T1 -> t gs gs T2) -> t gs gs T2
  | AndThenFS T1 T2 : t fs fs T1 -> (T1 -> t fs fs T2) -> t fs fs T2
  | AndThenDS T1 T2 : t ds ds T1 -> (T1 -> t ds ds T2) -> t ds ds T2
  | AndThenGB T1 T2 : t gb gb T1 -> (T1 -> t gb gb T2) -> t gb gb T2

  (* zooms *)
  | CallGS T : t gs gs T -> t es es T
  | ZoomFS T : t fs fs T -> t gs gs T
  | ZoomDS T : t ds ds T -> t fs fs T
  | ZoomGB T : t gb gb T -> t gs gs T
  | FstLiftES T : t nat nat T -> t es es T

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
  | RTerm.Pure ds t => Success X t
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
  | RTerm.AndThenDS r f =>
    let o := interpret_ds r X in
    match o with
    | Success b t => let r' := f t in let o' := interpret_ds r' b in o'
    | Error => Error
    | NotImpl => NotImpl
    end
  | RTerm.AllocPtr _ prm => 
    let p := snd X
                 in let f := @set ds (DynMap goModel.(@Ptr) Data.ptrModel) Data.allocs _ (updDyn p (Unlocked, prm))
                        in Success (f (fst X), (snd X) + 1) p
  | RTerm.UpdAllocs p pm =>
    let f := @set Data.State _ Data.allocs _ (updDyn p pm)
                        in Success (f (fst X), snd X) tt
  | RTerm.DelAllocs p =>
    let f := @set Data.State _ Data.allocs _ (deleteDyn p)
                        in Success (f (fst X), snd X) tt
  | _ => NotImpl
  end.

Fixpoint interpret_fs (T : Type) (r : RTerm.t fs fs T) (X : fs*ptrMap) : Output (fs*ptrMap) T :=
  match r with
  | RTerm.Pure fs t => Success X t
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

Fixpoint interpret_gb (T : Type) (r : RTerm.t gb gb T) (X : gb*ptrMap) : Output (gb*ptrMap) T :=
  match r with
  | RTerm.ReadsGB f => Success X (f (fst X))
  | RTerm.ReadSomeGB f =>
      let t' := f (fst X) in match t' with
                        | Some t => Success X t
                        | None => Error
                        end
  | RTerm.AndThenGB r f =>
    let o := interpret_gb r X in
    match o with
    | Success b t => let r' := f t in let o' := interpret_gb r' b in o'
    | Error => Error
    | NotImpl => NotImpl
    end
  | _ => NotImpl
  end.
    
Fixpoint interpret_gs (T : Type) (r : RTerm.t gs gs T) (X : gs*ptrMap) : Output (gs*ptrMap) T :=
  match r with
  | RTerm.Pure gs t => Success X t
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
  | RTerm.ZoomGB r => let (g, pm) := X in
                      let b := Go.maillocks g in
                      match (interpret_gb r (b, pm)) with
                      | Success (b', pm') t => Success (g <| Go.maillocks := b' |>, pm') t
                      | Error => Error
                      | NotImpl => NotImpl
                      end
  | RTerm.Error _ _ _ => (Error)
  | RTerm.NotImpl _ => NotImpl
  | _ => NotImpl
  end.

Fixpoint interpret_nat (T : Type) (r : RTerm.t nat nat T) (X : nat*ptrMap) : Output (nat*ptrMap) T :=
  match r with
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
  | RTerm.FstLiftES r => let (e, pm) := X in
                    let (thr, g) := e in
                    match (interpret_nat r (thr, pm)) with
                    | Success (thr', pm') t => Success ((thr', g), pm') t
                    | Error => Error                                                  
                    | NotImpl => NotImpl                                                  
                    end
  | _ => NotImpl
  end.

Fixpoint rtermDenote A B T (r: RTerm.t A B T) : relation A B T :=
  match r with
  | RTerm.Reads f => reads f
  | RTerm.ReadSome f => readSome f
  | RTerm.ReadsGB f => reads f
  | RTerm.ReadSomeGB f => readSome f
  | RTerm.ReadNone f => readNone f
  | RTerm.Puts f => puts f
  | RTerm.AllocPtr _ prm => Data.allocPtr _ prm
  | RTerm.UpdAllocs p pm => Data.updAllocs p pm
  | RTerm.DelAllocs  p => Data.delAllocs p

  | RTerm.Pure A o0 => pure o0
  | RTerm.Ret x => pure x
  | RTerm.BindES r1 f => and_then (rtermDenote r1) (fun x => (rtermDenote (f x)))
  | RTerm.AndThenGS r1 f => and_then (rtermDenote r1) (fun x => (rtermDenote (f x)))
  | RTerm.AndThenFS r1 f => and_then (rtermDenote r1) (fun x => (rtermDenote (f x)))
  | RTerm.AndThenDS r1 f => and_then (rtermDenote r1) (fun x => (rtermDenote (f x)))
  | RTerm.AndThenGB r1 f => and_then (rtermDenote r1) (fun x => (rtermDenote (f x)))

  | RTerm.CallGS r => snd_lift (rtermDenote r)
  | RTerm.ZoomFS r => _zoom Go.fs (rtermDenote r)
  | RTerm.ZoomDS r => _zoom FS.heap (rtermDenote r)
  | RTerm.ZoomGB r => _zoom Go.maillocks (rtermDenote r)
  | RTerm.FstLiftES r => fst_lift (rtermDenote r)

  | RTerm.Error _ _ _ => error
  | RTerm.NotImpl r => r
  end.

Ltac refl' RetB RetT e :=
  match eval simpl in e with
  | fun x : ?T => @reads ds ?T0 (@?f x) =>
    constr: (fun x => RTerm.Reads (f x))
  | fun x : ?T => @readSome ds ?T0 (@?f x) =>
    constr: (fun x => RTerm.ReadSome (f x))
  | fun x : ?T => @reads ?s ?T0 (@?f x) =>
    constr: (fun x => RTerm.ReadsGB (f x))
  | fun x : ?T => @readSome ?s ?T0 (@?f x) =>
    constr: (fun x => RTerm.ReadSomeGB (f x))
  | fun x : ?T => @readNone ?A ?T0 (@?f x) =>
    constr: (fun x => RTerm.ReadNone (f x))
  | fun x : ?T => @puts fs (@?f x) =>
    constr: (fun x => RTerm.Puts (f x))
              
  | fun x: ?T => @Data.allocPtr _ _ (@?ty x) (@?prm x) =>
    constr:(fun x => @RTerm.AllocPtr (ty x) (prm x))
  | fun x: ?T => @Data.updAllocs _ _ ?ty ?p ?pm =>
    constr: (fun x => RTerm.UpdAllocs ty p pm)
  | fun x: ?T => @Data.delAllocs _ _ ?ty ?p =>
    constr: (fun x => RTerm.DelAllocs ty p)

  | fun x : ?T => @pure ?A _ (@?E x) =>
    constr: (fun x => RTerm.Ret es (E x))
  | fun x : ?T => @pure ?A _ (@?E x) =>
    constr: (fun x => RTerm.Pure A (E x))

  | fun x: ?T => @and_then ?A ?B ?C ?T1 ?T2 (@?r1 x) (fun (y: ?T1) => (@?r2 x y)) =>
    let f1 := refl' B T1 r1 in
    let f2 := refl' C T2 (fun (p: T * T1) => (r2 (fst p) (snd p))) in
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
  | fun x: ?T => @and_then ?A ?B ?C ?T1 ?T2 (@?r1 x) (fun (y: ?T1) => (@?r2 x y)) =>
    let f1 := refl' B T1 r1 in
    let f2 := refl' C T2 (fun (p: T * T1) => (r2 (fst p) (snd p))) in
    constr: (fun x => RTerm.AndThenGB (f1 x) (fun y => f2 (x, y)))

  | fun x: ?T => @snd_lift ?A1 ?A2 ?B ?T1 (@?r x) =>
    let f := refl' A2 T1 r in
    constr: (fun x => RTerm.CallGS (f x))
  | (fun x: ?T => @_zoom gs fs Go.fs _ ?T1 (@?r1 x)) =>
    let f := refl' fs T1 r1 in
    constr: (fun x: T => RTerm.ZoomFS (f x))
  | (fun x: ?T => @_zoom fs ds FS.heap _ ?T1 (@?r1 x)) =>
    let f := refl' ds T1 r1 in
    constr: (fun x: T => RTerm.ZoomDS (f x))
  | (fun x: ?T => @_zoom ?s1 ?s2 Go.maillocks _ ?T1 (@?r1 x)) =>
    let f := refl' s2 T1 r1 in
    constr: (fun x: T => RTerm.ZoomGB (f x))
  | fun x: ?T => @fst_lift ?A1 ?A2 ?B ?T1 (@?r x) =>
    let f := refl' A2 T1 r in
    constr: (fun x => RTerm.FstLiftES (f x))

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

Ltac reflproc p :=
  let t := eval simpl in (Proc.exec_step Go.sem p) in
  refl t.

Definition reify_proc T (p : proc T)  : RTerm.t es es (proc T * thread_pool Op).
  destruct p eqn:?;
  match goal with
  | [ H : p = ?A |- _ ] => let x := reflproc A in idtac x; exact x
  end.
  (* match goal with
  | [ H : p = ?A |- _ ] => let t := constr:(@snd_lift _ _ nat T (Go.step op)) in
                               match constr:(fun _:unit => t) with
                               | fun x: ?T => @snd_lift ?A1 ?A2 ?B ?T1 (@?r x) =>
                                 let f := refl' A2 T1 r in
                                 idtac r
                               | _ => idtac t
                               end
  end. *)
Qed.
    
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
Proof.
  intros.
  pose (interpret r a).
  destruct interpret.
  - induct r.
    admit.
Admitted.

(* Tests *)    
Definition literalCast {model:GoModel} : proc uint64 :=
  let x := 2 in
  Ret (x + 2).

Definition usePtr {model:GoModel} : proc unit :=
  p <- Data.newPtr uint64;
  _ <- Data.writePtr p 1;
  x <- Data.readPtr p;
  Data.writePtr p x.

Module Table.
  (* A Table provides access to an immutable copy of data on the filesystem,
     along with an index for fast random access. *)
  Record t {model:GoModel} := mk {
    Index: Map uint64;
    File: File;
  }.
  Arguments mk {model}.
  Global Instance t_zero {model:GoModel} : HasGoZero t := mk (zeroValue _) (zeroValue _).
End Table.

(* CreateTable creates a new, empty table. *)
Definition CreateTable {model:GoModel} (p:string) : proc Table.t :=
  index <- Data.newMap uint64;
  let! (f, _) <- FS.create "db" p;
  _ <- FS.close f;
  f2 <- FS.open "db" p;
  Ret {| Table.Index := index;
         Table.File := f2; |}.

Goal False.
  pose CreateTable.
  let t := reflproc (p "table") in pose t.
  Compute (interpret t).
  pose literalCast.
  let t1 := reflproc p0 in pose t.
  Compute (interpret t0).
Admitted.
  
Ltac test e :=
  let t := refl e in
  let e' := eval cbv [rtermDenote] in (rtermDenote t) in
  unify e e'.
