From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement Require Import Helpers.MachinePrimitives.
From RecoveryRefinement Require Import Helpers.RelationAlgebra.
From RecoveryRefinement Require Import Database.Base.

From stdpp Require gmap.
From stdpp Require Import fin_maps.


Module MailServerSpec.

  Inductive Op : Type -> Type :=
  | Deliver (msg : ByteString) : Op unit
  | Pickup : Op (list (Path * ByteString))
  | Delete (id : Path) : Op unit.

  Definition State := gmap Path ByteString.

  Import RelationNotations.

  Definition step T (op:Op T) : relation State State T :=
    match op in Op T return relation State State T with
    | Deliver msg =>
      id <- such_that (fun s id => s !! id = None);
      puts (map_insert id msg)
    | Pickup =>
      reads map_to_list
    | Delete id =>
      puts (map_delete id)
    end.

  Definition crash_step : relation State State unit :=
    pure tt.

End MailServerSpec.
