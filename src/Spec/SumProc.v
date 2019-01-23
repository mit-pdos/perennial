From RecoveryRefinement Require Import Spec.Proc.

Set Implicit Arguments.

Inductive OpSum (Op1 Op2: Type -> Type) : Type -> Type :=
| Inl : forall T, Op1 T -> OpSum Op1 Op2 T
| Inr : forall T, Op2 T -> OpSum Op1 Op2 T.

Arguments Inl {Op1 Op2} {T}.
Arguments Inr {Op1 Op2} {T}.

Infix "⊕" := OpSum (at level 60).

Class Injectable (Op1 Op: Type -> Type) :=
  inject : forall T, Op1 T -> Op T.

Arguments inject {Op1 Op _ T}.

Instance Inl_inject Op1 Op2 : Injectable Op1 (Op1 ⊕ Op2) := @Inl _ _.
Instance Inr_inject Op1 Op2 : Injectable Op2 (Op1 ⊕ Op2) := @Inr _ _.

Fixpoint lift Op1 Op {i:Injectable Op1 Op} T (p: proc Op1 T) : proc Op T :=
  match p with
  | Call op => Call (inject op)
  | Ret v => Ret v
  | Bind p1 p2 => Bind (lift p1) (fun v => lift (p2 v))
  | Loop body init => Loop (fun v => lift (body v)) init
  | Spawn _ p => Spawn _ (lift p)
  end.
