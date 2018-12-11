From RecoveryRefinement Require Import Lib.
From stdpp Require Import gmap nmap.
Require Export Maybe.
Require Export Disk.
Require Export MVar.

Import RelationNotations.

(**
TwoDiskAPI supports reading and writing to two disks. It also allows one
disk to fail at any time (just before any operation). Note that disk failure is
separate from program crashes: programs can still crash and recover. In this
model, there is no way to recover from a disk failure (that is, we have a
fail-stop model).

*)

Module TwoDisk.
  Inductive diskId :=
  | d0
  | d1.

  Inductive DiskResult T :=
  | Working (v:T)
  | Failed.

  Arguments Failed {T}.

  Inductive DiskState :=
  | BothDisks (d_0:disk) (d_1:disk)
  | OnlyDisk0 (d_0:disk)
  | OnlyDisk1 (d_1:disk).

  (* TODO: might be better to use a finite dom. map type that lets values
     depend on a type index in the keys *)
  Definition MemState := gmap {T : Type & mvar T} {T : Type & option T}.

  (* These will be extracted to an immutable array, but we model them as a list *)
  Definition LockArray := list (mvar unit).

  Record ValidState := { disks : DiskState; mem : MemState; locks : LockArray;  }.

  Inductive State := Valid (vs: ValidState) | Error.

  Definition disk0 (state:DiskState) : option disk :=
    match state with
    | BothDisks d_0 _ => Some d_0
    | OnlyDisk0 d => Some d
    | OnlyDisk1 _ => None
    end.

  Definition disk1 (state:DiskState) : option disk :=
    match state with
    | BothDisks _ d_1 => Some d_1
    | OnlyDisk0 _ => None
    | OnlyDisk1 d => Some d
    end.

  Definition get_disk' (i:diskId) (state:DiskState) : option disk :=
    match i with
    | d0 => disk0 state
    | d1 => disk1 state
    end.

  Definition set_disk' (i:diskId) (state:DiskState) (d:disk) : DiskState :=
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

  Definition get_disk (i: diskId) (state:State) : option disk :=
    match state with
      | Valid vs => get_disk' i (disks vs)
      | _ => None
    end.

  Definition set_disk (i: diskId) (state:State) (d:disk) : State :=
    match state with
    | Valid state => Valid {| disks := set_disk' i (disks state) d;
                              mem := mem state;
                              locks := locks state |}
    | _ => Error
    end.

  Inductive Op : Type -> Type :=
  | op_read (i : diskId) (a : addr) : Op (DiskResult block)
  | op_write (i : diskId) (a : addr) (b : block) : Op (DiskResult unit)
  | op_size (i : diskId) : Op (DiskResult nat)
  | op_get_array (a : nat) : Op (mvar unit)
  | op_put_mvar {T : Type} (m: mvar T) (v: T) : Op unit
  | op_take_mvar {T : Type} (m: mvar T) : Op T
  | op_new_mvar {T : Type} (v: T) : Op (mvar T).

  Definition set_mem (state:State) (new_mem: MemState) : State :=
    match state with
    | Valid state => Valid {| disks := disks state; mem := new_mem; locks := locks state |}
    | _ => Error
    end.

  Print Instances Lookup.
  Inductive op_step : OpSemantics Op State :=
  | step_read : forall a i r state,
      match get_disk i state with
      | Some d => match index d a with
                  | Some b0 => r = Working b0
                  | None => exists b, r = Working b
                  end
      | None => r = Failed
      end ->
      op_step (op_read i a) state state r
  | step_write : forall a i b state r state',
      match get_disk i state with
      | Some d => state' = set_disk i state (assign d a b) /\
                  r = Working tt
      | None => r = Failed /\ state' = state
      end ->
      op_step (op_write i a b) state state' r
  | step_size : forall i state r,
      match get_disk i state with
      | Some d => r = Working (length d)
      | None => r = Failed
      end ->
      op_step (op_size i) state state r
  (* TODO: need to represent looping by not being able to take a step,
     so need explicit errors / identifying good states *)
  | step_new_mvar : forall {T: Type} (m: mvar T) (t: T) (state: ValidState),
      (* for some reason type class inference fails if the !! notation is used *)
      gmap_lookup (existT T m) (mem state) = None →
      op_step (op_new_mvar t) (Valid state)
              (set_mem (Valid state) (<[existT T m := existT T (Some t)]>(mem state)))
              m
  | step_put_mvar : forall {T T': Type} (m: mvar T) (t: T) state,
      mem state !! (existT _ m) = Some (existT T' None) →
      op_step (op_put_mvar m t) (Valid state)
              (set_mem (Valid state) (<[existT _ m := existT _ (Some t)]>(mem state)))
              tt
  | step_put_mvar_err : forall {T T': Type} (m: mvar T) (t: T) state,
      gmap_lookup (existT T m) (mem state) = None → 
      op_step (op_put_mvar m t) (Valid state)
              Error
              tt
  | step_take_mvar : forall {T: Type} (m: mvar T) (t: T) state,
      mem state !! (existT T m) = Some (existT T (Some t)) →
      op_step (op_take_mvar m) (Valid state)
              (set_mem (Valid state) (<[existT _ m := existT T None]>(mem state)))
              t
  | step_take_mvar_err : forall {T T': Type} (m: mvar T) (t: T) state,
      gmap_lookup (existT T m) (mem state) = None → 
      op_step (op_take_mvar m) (Valid state)
              Error
              tt.

  Inductive bg_failure' : DiskState -> DiskState -> unit -> Prop :=
  | step_id : forall (state: DiskState), bg_failure' state state tt
  | step_fail0 : forall d_0 d_1,
      bg_failure' (BothDisks d_0 d_1) (OnlyDisk1 d_1) tt
  | step_fail1 : forall d_0 d_1,
      bg_failure' (BothDisks d_0 d_1) (OnlyDisk0 d_0) tt.

  Definition bg_failure (state state': State) (u: unit) : Prop :=
    bg_failure' (disks state) (disks state') u /\
    mem state = mem state' /\
    locks state = locks state'.

  Definition pre_step {opT State}
             (bg_step: State -> State -> unit -> Prop)
             (step: OpSemantics opT State) :
    OpSemantics opT State :=
    fun T (op: opT T) state state'' v =>
      exists state', bg_step state state' tt /\
                     step _ op state' state'' v.

  Definition combined_step := pre_step bg_failure (@op_step).

  (* TODO need to init memory so that lock array is valid *)
  Definition TDBaseDynamics : Dynamics Op State :=
    {| step := op_step; crash_step := fun s1 s2 tt => disks s1 = disks s2 ∧
                                                      mem s2 = ∅ |}.

  Definition td_init (s: State) :=
    exists d_0' d_1',
      disk0 (disks s) ?|= eq d_0' /\
      disk1 (disks s) ?|= eq d_1' /\
      mem s = ∅.

  (*
  Lemma td_init_alt s: td_init s <-> True.
  Proof.
    split; auto; intros.
    destruct s as [d0 d1 | d | d].
    - repeat eexists; try congruence.
    - exists d, d. firstorder.
    - exists d, d. firstorder.
  Qed.
   *)

  Lemma crash_total_ok (s: State):
    exists s', TDBaseDynamics.(crash_step) s s' tt.
  Proof. exists {| disks := disks s; mem := ∅; locks := locks s|}. econstructor; eauto. Qed.

  Definition TDLayer : Layer Op :=
    {| Layer.State := State;
       sem := TDBaseDynamics;
       trace_proj := fun _ => nil;
       crash_preserves_trace := fun _ _ _ => eq_refl;
       crash_total := crash_total_ok;
       initP := td_init |}.

End TwoDisk.

(* Wrappers around the primitive operations *)
Module td.
  Import TwoDisk.
  Definition read i a : proc Op (DiskResult block) := Call (op_read i a).
  Definition write i a b : proc Op (DiskResult unit) := Call (op_write i a b).
  Definition size i : proc Op (DiskResult nat) := Call (op_size i).
End td.
