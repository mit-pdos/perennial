From Coq Require Import List.

Require Import RecoveryRefinement.POCS.
Require Import Spec.WeakestPreconditions.
Require Import Spec.WpRefine.

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
         (sum <- read Var.Sum; _ <- write Var.Sum (n + sum)%nat;
       count <- read Var.Count; _ <- write Var.Count (1 + count)%nat;
       Ret tt)%proc
       | DB.Avg =>
         (sum <- read Var.Sum; count <- read Var.Count; Ret (sum/count)%nat)%proc
       end;
     recover := Ret tt;
     init := Ret Initialized; |}.

Definition absr : relation DB.l.(State) Var.l.(State) unit :=
  fun l s _ =>
    fst s = fold_right plus 0 l /\
    snd s = length l.

Definition wp : WPSetup Var.dynamics.
Proof.
  refine {| op_wp T (op: Var.Op T) :=
              match op with
              | Var.Read i => fun post s => post (Var.get i s) s
              | Var.Write i v => fun post s => post tt (Var.set i v s)
              end |}.
  hnf; intros.
  destruct op; simpl in *; unfold reads, puts in *; propositional.
  destruct v; eauto.
Defined.

Definition rf : LayerRefinement Var.l DB.l.
Proof.
  refine {| Layer.impl := impl;
            Layer.absr := absr; |}.
  - red; intros.
    split.
    + eapply (wp.(wp_refine)); intros.
      destruct s as [sum' count'].
      unfold absr in H; simpl in *; propositional.
      destruct op; simpl.
      * (* read *)
        unfold puts; descend; intuition eauto.
        unfold absr; simpl; intuition eauto.
      * unfold reads; descend; intuition eauto.
        unfold absr; intuition eauto.
    + admit. (* rexec refinement *)
  - red; intros.
    eapply refine_unfolded; unfold absr; propositional.
    destruct s as [sum count]; simpl in *; propositional.
    destruct v.
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
