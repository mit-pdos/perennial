Require Import POCS.
Require Export Maybe.
Require Export TwoDiskBaseAPI.

(**
TwoDiskAPI supports reading and writing to two disks, with the possibility for a
disk to fail at any time. This layer provides easier-to-use specifications
written in terms of [maybe_holds] (the ?|= notation). The fact that at least one
disk is always functioning is encoded in the inductive type [TwoDiskBaseAPI.State]
itself; it has only three cases, for both disks, only disk 0, and only disk 1.
*)


Definition other (i : diskId) :=
  match i with
  | d0 => d1
  | d1 => d0
  end.

Definition read_spec (i : diskId) (a : addr) : _ -> Specification _ (unit) State :=
  fun '(d, F) state => {|
    pre :=
      get_disk i         state ?|= eq d /\
      get_disk (other i) state ?|= F;
    post := fun state' r =>
      match r with
      | Working v =>
        get_disk i         state' ?|= eq d /\
        get_disk (other i) state' ?|= F /\
        diskGet d a ?|= eq v
      | Failed =>
        get_disk i         state' ?|= missing /\
        get_disk (other i) state' ?|= F
      end;
    alternate := fun state' r =>
      get_disk i         state' ?|= eq d /\
      get_disk (other i) state' ?|= F;
  |}.

Definition write_spec (i : diskId) (a : addr) (b : block) : _ -> Specification (DiskResult unit) unit _ :=
  fun '(d, F) state => {|
    pre :=
      get_disk i         state ?|= eq d /\
      get_disk (other i) state ?|= F;
    post := fun state' r =>
      match r with
      | Working _ =>
        get_disk i         state' ?|= eq (diskUpd d a b) /\
        get_disk (other i) state' ?|= F
      | Failed =>
        get_disk i         state' ?|= missing /\
        get_disk (other i) state' ?|= F
      end;
    alternate := fun state' _ =>
      (get_disk i state' ?|= eq d \/
       get_disk i state' ?|= eq (diskUpd d a b) /\ a < diskSize d) /\
      get_disk (other i) state' ?|= F;
  |}.

Definition size_spec (i : diskId) : _ -> Specification _ unit _ :=
  fun '(d, F) state => {|
    pre :=
      get_disk i         state ?|= eq d /\
      get_disk (other i) state ?|= F;
    post := fun state' r =>
      match r with
      | Working n =>
        get_disk i         state' ?|= eq d /\
        get_disk (other i) state' ?|= F /\
        n = diskSize d
      | Failed =>
        get_disk i         state' ?|= missing /\
        get_disk (other i) state' ?|= F
      end;
    alternate := fun state' _ =>
      get_disk i         state' ?|= eq d /\
      get_disk (other i) state' ?|= F;
  |}.


Module Type TwoDiskAPI.

  (*
  Axiom init : proc InitResult.
   *)
  
  Axiom read : diskId -> addr -> proc Op (DiskResult block).
  Axiom write : diskId -> addr -> block -> proc Op (DiskResult unit).
  Axiom size : diskId -> proc Op (DiskResult nat).
  Axiom recover : proc Op unit.

  (*
  Axiom abstr : Abstraction State.
   *)

  (*
  Axiom init_ok : init_abstraction init recover abstr inited_any.
   *)

  Axiom read_ok : forall i a dF, proc_cspec TDBaseDynamics (read i a) (read_spec i a dF).
  Axiom write_ok : forall i a v dF, proc_cspec TDBaseDynamics (write i a v) (write_spec i a v dF).
  Axiom size_ok : forall i dF, proc_cspec TDBaseDynamics (size i) (size_spec i dF).
  Axiom recover_noop : rec_noop TDBaseDynamics recover eq.

  Hint Resolve init_ok.
  Hint Resolve read_ok.
  Hint Resolve write_ok.
  Hint Resolve size_ok.
  Hint Resolve recover_noop.

End TwoDiskAPI.