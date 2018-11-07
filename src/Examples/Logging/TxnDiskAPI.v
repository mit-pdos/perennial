Require Import POCS.
Require Export Maybe Disk.

Module TxnDisk.

  Definition State: Type := disk * disk.

  Inductive WriteStatus := WriteOK | WriteErr.

  Inductive Op : Type -> Type :=
  | op_commit : Op unit
  | op_read (a : addr) : Op block
  | op_write (a : addr) (b : block) : Op WriteStatus
  | op_size : Op nat.

  Inductive op_step : OpSemantics Op State :=
  | step_commit : forall d_old d,
      op_step (op_commit) (d_old, d) (d, d) tt
  | step_read : forall a r d_old d,
      (* note that we read from the old disk - this allows the log to serve
      reads directly from the data region rather than from the log (which in
      practice is done with an in-memory cache of the log) *)
      match index d_old a with
      | Some b0 => r = b0
      | None => exists b, r = b
      end ->
      op_step (op_read a) (d_old, d) (d_old, d) r
  | step_write_success : forall a b d_old d d',
      d' = (assign d a b) ->
      op_step (op_write a b) (d_old, d) (d_old, d') WriteOK
  | step_write_fail : forall a b d_old d,
      op_step (op_write a b) (d_old, d) (d_old, d) WriteErr
  | step_size : forall d_old d,
      (* it's an invariant of the log that the disks have the same size *)
      op_step (op_size) (d_old, d) (d_old, d) (length d).

  Definition dyn : Dynamics Op State :=
    {| step := op_step; crash_step := pure tt |}.

  Definition l : Layer Op :=
    {| Layer.State := State; sem := dyn; initP := fun '(d_old, d) => d_old = d |}.

End TxnDisk.
