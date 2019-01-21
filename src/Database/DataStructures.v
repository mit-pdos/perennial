From RecoveryRefinement Require Import Helpers.MachinePrimitives.
From RecoveryRefinement Require Import Spec.Proc.
From RecoveryRefinement Require Import Spec.SumProc.
From RecoveryRefinement Require Import Helpers.RelationAlgebra.

From RecordUpdate Require Import RecordSet.
Import ApplicativeNotations.

From Classes Require Import EqualDec.
From Coq Require Import NArith.
Import EqNotations.

Set Implicit Arguments.

Module ty.
  Inductive t : Type :=
  | Fd
  | uint64
  | uint32
  | ByteString
  | prod (A B:t)
  .
End ty.

Delimit Scope type_code_scope with ty.
Infix "*" := (ty.prod) : type_code_scope.

Definition ty := ty.t.

Fixpoint Ty (T:ty) : Type :=
  match T with
  | ty.Fd => Fd
  | ty.uint64 => uint64
  | ty.uint32 => uint32
  | ty.ByteString => ByteString
  | ty.prod A B => prod (Ty A) (Ty B)
  end.

Coercion Ty : ty >-> Sortclass.

Axiom IORef_ : Type.
Axiom ioref_eqdec : EqualDec IORef_.
Existing Instance ioref_eqdec.
Definition IORef (T:ty) := IORef_.

Axiom Array_ : Type.
Axiom array_eqdec : EqualDec Array_.
Existing Instance array_eqdec.
Definition Array (T:ty) := Array_.

Module Var.
  Inductive t :=
  | LogFile
  .

  Definition ty (x:t) : Type :=
    match x with
    | LogFile => Fd
    end.
End Var.

Instance var_eqdec : EqualDec Var.t := _.

Module Data.
  Inductive Op : Type -> Type :=
  (* generic variable operations *)
  | GetVar : forall (v:Var.t), Op (Var.ty v)
  | SetVar : forall (v:Var.t), Var.ty v -> Op unit

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

  Definition get Op' {i:Injectable Op Op'} (var: Var.t) : proc Op' (Var.ty var) :=
    Call (inject (GetVar var)).

  Definition set_var Op' {i:Injectable Op Op'} (var: Var.t) (v: Var.ty var) : proc Op' unit :=
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

  Definition arrayLength Op' {i:Injectable Op Op'} T (a: Array T) : proc Op' uint64 :=
    Call (inject (ArrayLength a)).

  Definition arrayGet Op' {i:Injectable Op Op'} T (a: Array T) (ix:uint64) : proc Op' T :=
    Call (inject (ArrayGet a ix)).

  Record State : Type :=
    mkState { vars: forall (var:Var.t), Var.ty var;
              iorefs: IORef_ -> option {T:ty & T};
              arrays: Array_ -> option {T:ty & list T};
              (* TODO: similar model for variables (except complete map) and
              arrays *) }.

  Instance _eta : Settable _ :=
    mkSettable (constructor mkState <*> vars <*> iorefs <*> arrays)%set.

  Definition upd_vars (var: Var.t) (v: Var.ty var) (vars: forall var, Var.ty var) :
    forall var, Var.ty var :=
    fun var' => match equal var var' with
             | left H => rew [Var.ty] H in v
             | right _ => vars var'
             end.

  Definition upd_iorefs T (v: IORef T) (x: T)
             (f:IORef_ -> option {T:ty & T}) : IORef_ -> option {T:ty & T}
    := fun r => if equal r v then Some (existT T x) else f r.

  Definition get_ioref T (v: IORef T)
             (f:IORef_ -> option {T:ty & T}) : option T :=
    match f v with
    | Some (existT T' x) =>
      match equal T' T with
      | left H => Some (rew [Ty] H in x)
      | right _ => None
      end
    | None => None
    end.

  Definition get_array T (v: Array T)
             (f: Array_ -> option {T:ty & list T}) : option (list T) :=
    match f v with
    | Some (existT T' x) =>
      match equal T' T with
      | left H => Some (rew [fun (T:ty) => list T] H in x)
      | right _ => None
      end
    | None => None
    end.

  Definition upd_arrays T (v: Array T) (x: list T)
             (f:Array_ -> option {T:ty & list T}) : Array_ -> option {T:ty & list T} :=
    fun r => if equal r v then Some (existT T x) else f r.

  Import RelationNotations.

  Definition step T (op:Op T) : relation State State T :=
    match op in Op T return relation State State T with
    | GetVar v => reads (fun s => vars s v)
    | SetVar v x => puts (set vars (upd_vars v x))
    | NewIORef _ x =>
      r <- such_that (fun s r => s.(iorefs) r = None);
        _ <- puts (set iorefs (upd_iorefs r x));
        pure r
    | WriteIORef v x =>
      _ <- readSome (fun s => get_ioref v s.(iorefs));
        puts (set iorefs (upd_iorefs v x))
    | ReadIORef v =>
      readSome (fun s => get_ioref v s.(iorefs))
    | NewArray T =>
      r <- such_that (fun s r => s.(arrays) r = None);
        _ <- puts (set arrays (upd_arrays r (@nil T)));
        pure r
    | ArrayAppend v x =>
      l0 <- readSome (fun s => get_array v s.(arrays));
        puts (set arrays (upd_arrays v (l0 ++ x::nil)))
    | ArrayLength v =>
      l <- readSome (fun s => get_array v s.(arrays));
        pure (uint64.(fromNum) (N.of_nat (length l)))
    | ArrayGet v i =>
      l0 <- readSome (fun s => get_array v s.(arrays));
        readSome (fun _ => List.nth_error l0 (N.to_nat (uint64.(toNum) i)))
    end.

End Data.

(* TODO: we should be able to make this pattern more convenient, but for now
calling withEnv results in worse syntax than a Bind (due to poor indentation)
and still requires calling lift over the second part. *)
Definition withEnv env (p: proc Data.Op env)
           Op' T (p': env -> proc Op' T)
           {i:Injectable Data.Op Op'} : proc Op' T :=
  Bind (lift p) p'.
