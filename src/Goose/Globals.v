From RecordUpdate Require Import RecordUpdate.
From Transitions Require Import Relations.

From Perennial Require Import Spec.Proc.
From Perennial Require Import Spec.InjectOp.
From Perennial.Goose Require Import Machine.

Set Implicit Arguments.

Module Globals.
  Section GoModel.
  Context `{model_wf: GoModelWf}.
  Context {G:Type}.
  Inductive Op : Type -> Type :=
  | SetX (x:G) : Op unit
  | GetX : Op G
  .

  Definition State := option G.
  Definition init : State := None.

  Import RelationNotations.

  Definition step T (op: Op T) : relation State State T :=
    match op in Op T return relation State State T with
    | SetX x => s <- reads id;
                 match s with
                 | Some _ => error
                 | None => puts (fun _ => Some x)
                 end
    | GetX => readSome id
    end.

  Section OpWrappers.
    Context {Op'} {i:Injectable Op Op'}.
    Notation proc := (proc Op').
    Notation "'Call' op" := (Call (inject op) : proc _) (at level 0).
    Notation "'Call!' op" := (Call op : proc _) (at level 0, op at level 200).

    Definition setX x := Call! SetX x.
    Definition getX := Call! GetX.
  End OpWrappers.
  End GoModel.
End Globals.

Arguments Globals.Op G : clear implicits.
Arguments Globals.State G : clear implicits.
