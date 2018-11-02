Require Import POCS.
Require Export Maybe Disk.

Definition State := disk.

Inductive OneDiskOp : Type -> Type :=
| op_read (a : addr) : OneDiskOp block
| op_write (a : addr) (b : block) : OneDiskOp unit
| op_size : OneDiskOp nat.

Inductive one_disk_op_step : OpSemantics OneDiskOp State :=
| step_read : forall a r state,
    match diskGet state a with
    | Some b0 => r = b0
    | None => exists b, r = b
    end ->
    one_disk_op_step (op_read a) state state r
| step_write : forall a b state state',
    state' = (diskUpd state a b) ->
    one_disk_op_step (op_write a b) state state' tt
| step_size : forall state,
    one_disk_op_step (op_size) state state (diskSize state).

Definition read_spec (a : addr) : _ -> Specification block unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun state' r =>
      state' = state /\
      diskGet state a ?|= eq r;
    alternate := fun state' r =>
      state' = state
  |}.

Definition write_spec (a : addr) (v : block) : _ -> Specification _ unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun state' r =>
      r = tt /\ state' = diskUpd state a v;
    alternate := fun state' r =>
      state' = state \/ state' = diskUpd state a v
  |}.

Definition size_spec : _ -> Specification nat unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun state' r =>
      state' = state /\ r = diskSize state;
    alternate := fun state' r =>
      state' = state
  |}.

Inductive one_disk_failure : CrashSemantics State :=
| step_id : forall (state: State), one_disk_failure state state tt.

Definition ODBaseDynamics : Dynamics OneDiskOp State :=
  {| step := one_disk_op_step; crash_step := one_disk_failure |}.

Definition ODLayer : Layer OneDiskOp :=
  {| Layer.State := State; sem := ODBaseDynamics; initP := fun _ => True |}.

