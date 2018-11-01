From Coq Require Import List.

Require Import RecoveryRefinement.POCS.
Require Import Spec.WeakestPreconditions.

Import RelationNotations.
Require Import Helpers.RelationRewriting.

Module Var.
  Inductive id := Sum | Count.
  Inductive Op : Type -> Type :=
  | Read (i:id) : Op nat
  | Write (i:id) (v:nat) : Op unit .
  Definition State := (nat * nat)%type.

  Definition get (i:id) : State -> nat :=
    match i with
    | Sum => fun '(x, _) => x
    | Count => fun '(_, y) => y
    end.

  Definition set (i:id) (v:nat) : State -> State :=
    match i with
    | Sum => fun '(_, y) => (v, y)
    | Count => fun '(x, _) => (x, v)
    end.

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
         match op with
         | Read i => reads (get i)
         | Write i v => puts (set i v)
         end;
       crash_step :=
         puts (fun _ => (0, 0)); |}.

  Definition l : Layer Op :=
    {| Layer.State := State;
       sem := dynamics;
       initP := fun s => s = (0, 0)|}.
End Var.

Module DB.
  Inductive Op : Type -> Type :=
  | Add (n:nat) : Op unit
  | Avg : Op nat.
  Definition State := list nat.

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
         match op with
         | Add n => puts (cons n)
         | Avg => reads (fun l => fold_right plus 0 l / length l)
         end;
       crash_step :=
         puts (fun _ => nil); |}.

  Definition l : Layer Op :=
    {| Layer.State := State;
       sem := dynamics;
       initP := fun s => s = nil |}.
End DB.

Definition read i := Prim (Var.Read i).
Definition write i v := Prim (Var.Write i v).

Definition impl : LayerImpl Var.Op DB.Op :=
  {| compile_op T (op: DB.Op T) :=
       match op with
       | DB.Add n =>
         (sum <- read Var.Sum; _ <- write Var.Sum (sum + n)%nat;
       count <- read Var.Count; _ <- write Var.Count (1 + count)%nat;
       Ret tt)%proc
       | DB.Avg =>
         (sum <- read Var.Sum; count <- read Var.Count; Ret (sum+count)%nat)%proc
       end;
     recover := Ret tt;
     init := Ret Initialized; |}.

Definition absr : relation DB.l.(State) Var.l.(State) unit :=
  fun l s _ =>
    fst s = fold_right plus 0 l /\
    snd s = length l.

Definition op_wp T (op: Var.Op T) : precondition Var.State T :=
    match op with
    | Var.Read i => fun post s => post (Var.get i s) s
    | Var.Write i v => fun post s => post tt (Var.set i v s)
    end.

Theorem op_wp_is_ok : op_wp_ok Var.dynamics op_wp.
Proof.
  hnf; intros.
  destruct op; simpl in *; unfold reads, puts in *; propositional.
  destruct v; eauto.
Qed.

Definition rf : LayerRefinement Var.l DB.l.
Proof.
  refine {| Layer.impl := impl;
            Layer.absr := absr; |}.
  - red; intros.
    split.
    + admit. (* exec refinement of impls *)
    + admit. (* rexec refinement of impls *)
  - red; intros.
    admit. (* recovery transfers crash step *)
  - (* initialize abstraction *) simpl.
    Left.
    unfold and_then, test, rimpl, pure, any, absr; simpl; propositional.
    descend; intuition eauto.
    descend; intuition eauto.
    descend; intuition eauto.
    simpl; auto.
    simpl; auto.
Abort.
