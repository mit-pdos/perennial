Require Import POCS.
Require Export Disk.

(**
TwoDiskBaseAPI supports reading and writing to two disks. It also allows one
disk to fail at any time (just before any operation). Note that disk failure is
separate from program crashes: programs can still crash and recover. In this
model, there is no way to recover from a disk failure (that is, we have a
fail-stop model).

We provide a more convenient set of specifications (for the same operations) in
TwoDiskAPI.
*)

Inductive diskId :=
| d0
| d1.

Inductive DiskResult T :=
| Working (v:T)
| Failed.

Arguments Failed {T}.

Inductive State :=
| BothDisks (d_0:disk) (d_1:disk)
| OnlyDisk0 (d_0:disk)
| OnlyDisk1 (d_1:disk).

Definition disk0 (state:State) : option disk :=
  match state with
  | BothDisks d_0 _ => Some d_0
  | OnlyDisk0 d => Some d
  | OnlyDisk1 _ => None
  end.

Definition disk1 (state:State) : option disk :=
  match state with
  | BothDisks _ d_1 => Some d_1
  | OnlyDisk0 _ => None
  | OnlyDisk1 d => Some d
  end.

Definition get_disk (i:diskId) (state:State) : option disk :=
  match i with
  | d0 => disk0 state
  | d1 => disk1 state
  end.

Definition set_disk (i:diskId) (state:State) (d:disk) : State :=
  match i with
  | d0 => match state with
         | BothDisks _ d_1 => BothDisks d d_1
         | OnlyDisk0 _ => OnlyDisk0 d
         | OnlyDisk1 d_1 => BothDisks d d_1
         end
  | d1 => match state with
         | BothDisks d_0 _ => BothDisks d_0 d
         | OnlyDisk0 d_0 => BothDisks d_0 d
         | OnlyDisk1 _ => OnlyDisk1 d
         end
  end.

Inductive Op : Type -> Type :=
| op_read (i : diskId) (a : addr) : Op (DiskResult block)
| op_write (i : diskId) (a : addr) (b : block) : Op (DiskResult unit)
| op_size (i : diskId) : Op (DiskResult nat).

Inductive op_step : OpSemantics Op State :=
| step_read : forall a i r state,
    match get_disk i state with
    | Some d => match diskGet d a with
               | Some b0 => r = Working b0
               | None => exists b, r = Working b
               end
    | None => r = Failed
    end ->
    op_step (op_read i a) state state r
| step_write : forall a i b state r state',
    match get_disk i state with
    | Some d => state' = set_disk i state (diskUpd d a b) /\
               r = Working tt
    | None => r = Failed /\ state' = state
    end ->
    op_step (op_write i a b) state state' r
| step_size : forall i state r,
    match get_disk i state with
    | Some d => r = Working (diskSize d)
    | None => r = Failed
    end ->
    op_step (op_size i) state state r.

Inductive bg_failure : CrashSemantics State :=
| step_id : forall (state: State), bg_failure state state tt
| step_fail0 : forall d_0 d_1,
    bg_failure (BothDisks d_0 d_1) (OnlyDisk1 d_1) tt
| step_fail1 : forall d_0 d_1,
    bg_failure (BothDisks d_0 d_1) (OnlyDisk0 d_0) tt.

Definition TDBaseDynamics : Dynamics Op State :=
  {| step := op_step; crash_step := bg_failure |}.

Definition TDLayer : Layer Op :=
  {| Layer.State := State; sem := TDBaseDynamics; initP := fun _ => True |}.

Module Type TwoDiskBaseAPI.

  (* XXX Need init *) 
  (*
  Axiom init : proc InitResult.
   *)
  Axiom read : diskId -> addr -> proc Op (DiskResult block).
  Axiom write : diskId -> addr -> block -> proc Op (DiskResult unit).
  Axiom size : diskId -> proc Op (DiskResult nat).
  Axiom recover : proc Op unit.

  (*
  Axiom abstr : Abstraction Op State.
   *)

  (* XXX Need init *) 
  (*
  Axiom init_ok : init_abstraction init recover abstr inited_any.
   *)

  Axiom read_ok :
    forall i a,
      proc_ok TDBaseDynamics (read i a) recover (op_spec TDBaseDynamics (op_read i a)).
  Axiom write_ok :
    forall i a b,
      proc_ok TDBaseDynamics (write i a b) recover (op_spec TDBaseDynamics (op_write i a b)).
  Axiom size_ok :
    forall i,
      proc_ok TDBaseDynamics  (size i) recover (op_spec TDBaseDynamics (op_size i)).
  Axiom recover_noop :
    rec_noop TDBaseDynamics recover eq.

  Hint Resolve init_ok.
  Hint Resolve read_ok.
  Hint Resolve write_ok.
  Hint Resolve size_ok.
  Hint Resolve recover_noop.

End TwoDiskBaseAPI.