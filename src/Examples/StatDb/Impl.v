From Coq Require Import List.

Require Export RecoveryRefinement.POCS.

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

Definition read i := Call (Var.Read i).
Definition write i v := Call (Var.Write i v).

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
