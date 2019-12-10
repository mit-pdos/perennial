From Coq Require Import List.

From Perennial Require Export Lib.
From Perennial.Examples Require Import ExMach.ExMachAPI.
Import RelationNotations.

Axiom log_size : nat.
Axiom log_size_ok : log_size + 1 ≤ ExMach.size.

Module Log2.

  Inductive Op : Type -> Type :=
  | Append (l: list nat) : Op bool
  | Read : Op (list nat).

  Definition State : Set := list nat.

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
         match op with
         | Append l' =>
            curl <- reads (fun l => l);
            ( pure false ) + 
            ( _ <- puts (fun l => l ++ l'); pure true )
         | Read => reads (fun l => l)
         end;
       crash_step := pure tt;
       finish_step := pure tt;
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
       finish_non_err := crash_non_err_ok;
       initP := fun s => s = nil |}.

End Log2.
