From Coq Require Import List.

From RecoveryRefinement Require Export Lib.


Module AtomicPair.
  Inductive Op : Type -> Type :=
  | Write (p: nat * nat) : Op unit
  | Read : Op (nat * nat).
  Definition State : Set := nat * nat.

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
         match op with
         | Write p => puts (fun _ => p)
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
       initP := fun s => s = (0, 0) |}.
End AtomicPair.