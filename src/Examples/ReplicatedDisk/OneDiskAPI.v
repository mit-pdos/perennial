From Coq Require Import List.

From stdpp Require Import gmap.
From Armada Require Export Lib.
From Armada Require Import TwoDiskAPI.

Module OneDisk.
  Definition disk := gmap addr nat.

  (* TODO: Add memory operations to this layer, or perhaps
     a disk CAS *)
  Inductive Op : Type -> Type :=
  | Read_Disk (i:addr) : Op nat
  | Write_Disk (i:addr) (v:nat) : Op unit.

  Record State := mkState { disk_state: disk }.

  Definition state_wf s :=
    wf_range (disk_state s).

  Definition lookup_default (i: addr) (s: gmap addr nat) : nat :=
    match s !! i with
    | Some n => n
    | None => 0
    end.

  Definition upd_default (i: addr) (v: nat) (s: gmap addr nat) : gmap addr nat :=
    match s !! i with
    | Some _ => <[i := v]>s
    | None => s
    end.

  Definition lookup_disk (i: addr) : State -> nat :=
    fun s => lookup_default i (disk_state s).

  Definition upd_disk (i: addr) (v: nat) :=
    fun s => {| disk_state := upd_default i v (disk_state s); |}.

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
         match op with
         | Read_Disk i => reads (lookup_disk i)
         | Write_Disk i v => puts (upd_disk i v)
         end;
       crash_step := pure tt;
       finish_step := pure tt |}.

  Lemma crash_total_ok (s: State):
    exists s', dynamics.(crash_step) s (Val s' tt).
  Proof. eexists; econstructor. Qed.

  Lemma crash_non_err_ok (s: State) ret:
    dynamics.(crash_step) s ret -> ret ≠ Err.
  Proof. inversion 1; congruence. Qed.

  Definition init_state :=
    {| disk_state := init_zero |}.

  Definition l : Layer Op :=
    {| Layer.OpState := State;
       sem := dynamics;
       trace_proj := fun _ => nil;
       crash_preserves_trace := fun _ _ _ => eq_refl;
       crash_total := crash_total_ok;
       finish_total := crash_total_ok;
       crash_non_err := crash_non_err_ok;
       finish_non_err := crash_non_err_ok;
       initP := fun s => s = init_state |}.
End OneDisk.