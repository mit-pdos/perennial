From RecoveryRefinement Require Import Helpers.MachinePrimitives.
From RecoveryRefinement Require Import Spec.Proc.
From RecoveryRefinement Require Import Spec.SumProc.

Set Implicit Arguments.

Axiom Array : Type -> Type.

Inductive Var : Type -> Type :=
| LogFd : Var Fd
| LogRecoveredTxns : Var (Array ByteString)
.

Module Data.
  Inductive Op : Type -> Type :=
  (* generic variable operations *)
  | GetVar : forall T, Var T -> Op T
  | SetVar : forall T, Var T -> T -> Op T

  (* arrays *)
  | NewArray : forall T, Op (Array T)
  | ArrayLength : forall T, Array T -> Op int64
  | ArrayGet : forall T, Array T -> int64 -> Op T
  | ArrayAppend : forall T, Array T -> T -> Op unit

  (* TODO: hashtables *)
  .

  Definition get Op' {i:Injectable Op Op'} T (var: Var T) : proc Op' T :=
    Call (inject (GetVar var)).

  Definition arrayAppend Op' {i:Injectable Op Op'} T (a: Array T) (v:T) : proc Op' unit :=
    Call (inject (ArrayAppend a v)).
End Data.

(* TODO: we should be able to make this pattern more convenient, but for now
calling withEnv results in worse syntax than a Bind (due to poor indentation)
and still requires calling lift over the second part. *)
Definition withEnv env (p: proc Data.Op env)
           Op' T (p': env -> proc Op' T)
           {i:Injectable Data.Op Op'} : proc Op' T :=
  Bind (lift p) p'.
