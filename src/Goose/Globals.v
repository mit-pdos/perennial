From RecordUpdate Require Import RecordUpdate.

From RecoveryRefinement Require Import Spec.Proc.
From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement.Goose Require Import Machine.

From RecoveryRefinement Require Import Helpers.RelationAlgebra.

Set Implicit Arguments.

Module Globals.
  Section GoModel.
  Context `{model_wf: GoModelWf}.
  Context {G:Type}.
  Inductive Op : Type -> Type :=
  | SetX (x:G) : Op unit
  | GetX : Op G
  .

  Definition State := G.

  Definition step T (op: Op T) : relation State State T :=
    match op in Op T return relation State State T with
    | SetX x => puts (fun _ => x)
    | GetX => reads id
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
