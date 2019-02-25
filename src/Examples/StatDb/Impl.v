From Coq Require Import List.

From RecoveryRefinement Require Export Lib.
Require Import ExMach.ExMachAPI.


Module DB.
  Inductive Op : Type -> Type :=
  | Add (n:nat) : Op unit
  | Avg : Op nat.
  Definition State := list nat.

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
         match op with
         | Add n => puts (cons n)
         | Avg => reads (fun l => fold_right plus 0 l / length l)
         end;
       crash_step :=
         puts (fun _ => nil);
       finish_step :=
         puts (fun _ => nil);
    |}.

  Lemma crash_total_ok (s: State):
    exists s', dynamics.(crash_step) s (Val s' tt).
  Proof. eexists; econstructor. Qed.

  Lemma crash_non_err_ok (s: State) ret:
    dynamics.(crash_step) s ret -> ret ≠ Err.
  Proof. inversion 1; congruence. Qed.

  Definition l : Layer Op :=
    {| Layer.OpState := State;
       sem := dynamics;
       trace_proj := fun _ => nil;
       crash_preserves_trace := fun _ _ _ => eq_refl;
       crash_total := crash_total_ok;
       finish_total := crash_total_ok;
       crash_non_err := crash_non_err_ok;
       initP := fun s => s = nil |}.
End DB.

Definition sum_addr := 0.
Definition count_addr := 1.
Definition lock_addr := 2.

Definition add n :=
  (_ <- lock lock_addr;
   sum <- read_mem sum_addr; _ <- write_mem sum_addr (n + sum)%nat;
   count <- read_mem count_addr; _ <- write_mem count_addr (1 + count)%nat;
   unlock lock_addr)%proc.

Definition avg :=
  (_ <- lock lock_addr;
   sum <- read_mem sum_addr; count <- read_mem count_addr;
   _ <- unlock lock_addr; Ret (sum/count)%nat)%proc.

Definition impl : LayerImpl ExMach.Op DB.Op :=
  {| compile_op T (op: DB.Op T) :=
       match op with
       | DB.Add n => add n
       | DB.Avg => avg
       end;
     recover := Seq_Cons (Ret tt) (Seq_Nil);
     (* init := Ret Initialized; *) |}.
