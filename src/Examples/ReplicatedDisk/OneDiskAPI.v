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

Definition read_spec (a : addr) : Specification _ block unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun state' r =>
      state' = state /\
      diskGet state a ?|= eq r;
    recovered := fun state' r =>
      state' = state
  |}.

Definition write_spec (a : addr) (v : block) : Specification _ _ unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun state' r =>
      r = tt /\ state' = diskUpd state a v;
    recovered := fun state' r =>
      state' = state \/ state' = diskUpd state a v
  |}.

Definition size_spec : Specification _ nat unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun state' r =>
      state' = state /\ r = diskSize state;
    recovered := fun state' r =>
      state' = state
  |}.

Inductive one_disk_failure : CrashSemantics State :=
| step_id : forall (state: State), one_disk_failure state state tt.

Definition ODBaseDynamics : Dynamics OneDiskOp State :=
  {| step := one_disk_op_step; crash_step := one_disk_failure |}.

Definition ODLayer : Layer OneDiskOp :=
  {| Layer.State := State; sem := ODBaseDynamics; initP := fun _ => True |}.

Module Type OneDiskAPI.

  (*
  Axiom init : proc InitResult.
   *)
  Axiom read : addr -> proc OneDiskOp block.
  Axiom write : addr -> block -> proc OneDiskOp unit.
  Axiom size : proc OneDiskOp nat.
  Axiom recover : proc OneDiskOp unit.

  (*
  Axiom abstr : Abstraction State.
   *)

  (*
  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom read_ok : forall a, proc_spec (read_spec a) (read a) recover abstr.
  Axiom write_ok : forall a v, proc_spec (write_spec a v) (write a v) recover abstr.
  Axiom size_ok : proc_spec size_spec size recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_wipe.

  Hint Resolve init_ok.
  Hint Resolve read_ok.
  Hint Resolve write_ok.
  Hint Resolve size_ok.
  Hint Resolve recover_noop.
  *)

End OneDiskAPI.
