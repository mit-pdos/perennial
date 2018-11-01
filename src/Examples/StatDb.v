Require Import RecoveryRefinement.POCS.
From Coq Require Import List.

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
         | Avg => reads (fun l => fold_left plus l 0 / length l)
         end;
       crash_step :=
         puts (fun _ => nil); |}.

  Definition l : Layer Op :=
    {| Layer.State := State;
       sem := dynamics;
       initP := fun s => s = nil |}.
End DB.
