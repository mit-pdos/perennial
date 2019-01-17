From RecoveryRefinement Require Import Helpers.MachinePrimitives.
From RecoveryRefinement Require Import Spec.Proc.
From RecoveryRefinement Require Import Spec.SumProc.
From RecoveryRefinement Require Import Helpers.RelationAlgebra.

From RecordUpdate Require Import RecordSet.
Import ApplicativeNotations.

From Classes Require Import EqualDec.
From Coq Require Import Program.Equality.
Import EqNotations.

Set Implicit Arguments.

Module ty.
  Inductive t : Type :=
  | Fd
  | uint64
  | ByteString
  .
End ty.

Definition ty := ty.t.

Coercion Ty (T:ty) : Type :=
  match T with
  | ty.Fd => Fd
  | ty.uint64 => uint64
  | ty.ByteString => ByteString
  end.

Axiom IORef_ : Type.
Axiom ioref_eqdec : EqualDec IORef_.
Existing Instance ioref_eqdec.

Definition IORef (T:ty) := IORef_.

(* TODO: fix Arrays to be same as IORef *)
Axiom Array : Type -> Type.

(* TODO: fix Vars to be same as IORef *)
Inductive LogVar : Type -> Type :=
| File : LogVar Fd
.

Inductive Var : Type -> Type :=
| Log : forall T, LogVar T -> Var T
.

Instance var_eqdec T : EqualDec (Var T).
Proof.
  hnf; intros.
  destruct x, y.
  - dependent destruction l; dependent destruction l0; auto.
Defined.

(* hetereogeneous equality of a type family *)
Class HEqDec A (F: A -> Type) :=
  heq_dec : forall a1 a2 (x: F a1) (y: F a2),
    {H & (rew H in x) = y} + {forall H, (rew H in x) <> y}.

Definition var_eq T1 T2 (x: Var T1) (y: Var T2) :
  {H & (rew H in x) = y} + {forall H, (rew H in x) <> y}.
Proof.
  destruct x, y.
  - dependent destruction l; dependent destruction l0.
    left.
    exists eq_refl; auto.
Defined.

Module Data.
  Inductive Op : Type -> Type :=
  (* generic variable operations *)
  | GetVar : forall T, Var T -> Op T
  | SetVar : forall T, Var T -> T -> Op T

  (* arbitrary references *)
  | NewIORef : forall (T:ty), T -> Op (IORef T)
  | ReadIORef : forall T, IORef T -> Op T
  | WriteIORef : forall T, IORef T -> T -> Op unit

  (* arrays *)
  | NewArray : forall T, Op (Array T)
  | ArrayLength : forall T, Array T -> Op uint64
  | ArrayGet : forall T, Array T -> uint64 -> Op T
  | ArrayAppend : forall T, Array T -> T -> Op unit

  (* TODO: hashtables *)
  .

  Definition get Op' {i:Injectable Op Op'} T (var: Var T) : proc Op' T :=
    Call (inject (GetVar var)).

  Definition set_var Op' {i:Injectable Op Op'} T (var: Var T) (v: T) : proc Op' T :=
    Call (inject (SetVar var v)).

  Definition newIORef Op' {i:Injectable Op Op'}
             (T:ty) (v:T) : proc Op' (IORef T) :=
    Call (inject (NewIORef T v)).

  Definition readIORef Op' {i:Injectable Op Op'}
             T (ref:IORef T) : proc Op' T :=
    Call (inject (ReadIORef ref)).

  Definition writeIORef Op' {i:Injectable Op Op'}
             T (ref:IORef T) (v:T) : proc Op' unit :=
    Call (inject (WriteIORef ref v)).

  (* non-atomic modify (we could add atomicModifyIORef' but I don't think we
  need it) *)
  Definition modifyIORef Op' {i:Injectable Op Op'}
             T (ref:IORef T) (f: T -> T) : proc Op' unit :=
    Bind (Call (inject (ReadIORef ref)))
         (fun x => Call (inject (WriteIORef ref (f x)))).

  Definition arrayAppend Op' {i:Injectable Op Op'} T (a: Array T) (v:T) : proc Op' unit :=
    Call (inject (ArrayAppend a v)).

  Record State : Type :=
    mkState { iorefs: IORef_ -> option {T:ty & T};
              (* TODO: similar model for variables (except complete map) and
              arrays *) }.

  Instance _eta : Settable _ :=
    mkSettable (constructor mkState <*> iorefs)%set.

  Definition upd_iorefs T (v: IORef T) (x: T)
             (f:IORef_ -> option {T:ty & T}) : IORef_ -> option {T:ty & T}
    := fun r => if equal r v then Some (existT T x) else f r.

  Definition get_ioref T (v: IORef T)
             (f:IORef_ -> option {T:ty & T}) : option T :=
    match f v with
    | Some (existT T' x) =>
      match equal T' T with
      | left H => Some (rew H in x)
      | right _ => None
      end
    | None => None
    end.

  Import RelationNotations.

  Definition step T (op:Op T) : relation State State T :=
    match op in Op T return relation State State T with
    (* | GetVar v => reads (fun s => vars s v) *)
    (* | SetVar v x => puts (set vars (fupd v x)) *)
    | NewIORef _ x =>
      r <- such_that (fun s r => s.(iorefs) r = None);
        _ <- puts (set iorefs (upd_iorefs r x));
        pure r
    | WriteIORef v x =>
      _ <- readSome (fun s => s.(iorefs) v);
        puts (set iorefs (upd_iorefs v x))
    | ReadIORef v =>
      readSome (fun s => get_ioref v s.(iorefs))
    | _ => error
    end.

End Data.

(* TODO: we should be able to make this pattern more convenient, but for now
calling withEnv results in worse syntax than a Bind (due to poor indentation)
and still requires calling lift over the second part. *)
Definition withEnv env (p: proc Data.Op env)
           Op' T (p': env -> proc Op' T)
           {i:Injectable Data.Op Op'} : proc Op' T :=
  Bind (lift p) p'.
