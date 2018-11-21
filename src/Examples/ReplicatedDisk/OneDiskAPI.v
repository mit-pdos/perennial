From RecoveryRefinement Require Import Lib.
Require Export Maybe Disk.

Module D.

  Definition State := disk.
  Inductive Op : Type -> Type :=
  | op_read (a : addr) : Op block
  | op_write (a : addr) (b : block) : Op unit
  | op_size : Op nat.

  Inductive op_step : OpSemantics Op State :=
  | step_read : forall a r state,
      match index state a with
      | Some b0 => r = b0
      | None => exists b, r = b
      end ->
      op_step (op_read a) state state r
  | step_write : forall a b state state',
      state' = (assign state a b) ->
      op_step (op_write a b) state state' tt
  | step_size : forall state,
      op_step (op_size) state state (length state).

  Inductive one_disk_failure : CrashSemantics State :=
  | step_id : forall (state: State), one_disk_failure state state tt.

  Definition ODBaseDynamics : Dynamics Op State :=
    {| step := op_step; crash_step := one_disk_failure |}.

  Definition ODLayer : Layer Op :=
    {| Layer.State := State; sem := ODBaseDynamics; initP := fun _ => True |}.

End D.
