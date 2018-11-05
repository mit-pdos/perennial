Require Import POCS.
Require Export Maybe Disk.


Module OneDisk.

  Definition State := disk.
  Inductive Op : Type -> Type :=
  | op_read (a : addr) : Op block
  | op_write (a : addr) (b : block) : Op unit
  | op_size : Op nat.

  Inductive op_step : OpSemantics Op State :=
  | step_read : forall a r state,
      match diskGet state a with
      | Some b0 => r = b0
      | None => exists b, r = b
      end ->
      op_step (op_read a) state state r
  | step_write : forall a b state state',
      state' = (diskUpd state a b) ->
      op_step (op_write a b) state state' tt
  | step_size : forall state,
      op_step (op_size) state state (diskSize state).

  Inductive one_disk_failure : CrashSemantics State :=
  | step_id : forall (state: State), one_disk_failure state state tt.

  Definition ODBaseDynamics : Dynamics Op State :=
    {| step := op_step; crash_step := one_disk_failure |}.

  Definition ODLayer : Layer Op :=
    {| Layer.State := State; sem := ODBaseDynamics; initP := fun _ => True |}.

End OneDisk.

Definition read_spec (a : addr) : Specification block unit OneDisk.State :=
  fun state => {|
    pre := True;
    post := fun state' r =>
      state' = state /\
      diskGet state a ?|= eq r;
    alternate := fun state' r =>
      state' = state
  |}.

Definition write_spec (a : addr) (v : block) : Specification _ unit OneDisk.State :=
  fun state => {|
    pre := True;
    post := fun state' r =>
      r = tt /\ state' = diskUpd state a v;
    alternate := fun state' r =>
      state' = state \/ state' = diskUpd state a v
  |}.

Definition size_spec : Specification nat unit OneDisk.State :=
  fun state => {|
    pre := True;
    post := fun state' r =>
      state' = state /\ r = diskSize state;
    alternate := fun state' r =>
      state' = state
  |}.
