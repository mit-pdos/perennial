From RecordUpdate Require Import RecordUpdate.

From RecoveryRefinement Require Export Lib.

Import RelationNotations.

Module Log.
  Inductive Op : Type -> Type :=
  | Append (txn: nat * nat) : Op unit
  | Commit : Op unit
  | GetLog (i: nat) : Op (option nat)
  .

  Record State : Type :=
    mkState { mem_buf : list nat;
              disk_log : list nat; }.

  Global Instance _eta : Settable _ :=
    mkSettable (constructor mkState <*> mem_buf <*> disk_log)%set.

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
         match op with
         | Append (v1, v2) =>
           puts (set mem_buf (fun l => l ++ [v1; v2]))
         | Commit =>
           l' <- reads mem_buf;
         puts (set disk_log (fun l => l ++ l'))
         | GetLog i => reads (fun s => nth_error (disk_log s) i)
         end;
       crash_step :=
         puts (set mem_buf (fun _ => []));
       finish_step :=
         l' <- reads mem_buf;
       puts (set disk_log (fun l => l ++ l'));
    |}.

  Global Instance empty_state : Empty State :=
    {| mem_buf := [];
       disk_log := [] |}.

  (* TODO: factor out these total/non-erroring theorems to typeclasses over
  relations with instances for reads, puts, and bind *)

  Lemma crash_total_ok s :
    exists s', dynamics.(crash_step) s (Val s' tt).
  Proof.
    eexists; econstructor.
  Qed.

  Lemma crash_non_err_ok s ret :
    dynamics.(crash_step) s ret -> ret <> Err.
  Proof.
    inversion 1; subst; simpl in *.
    discriminate.
  Qed.

  Definition l : Layer Op.
    refine {| Layer.OpState := State;
              sem := dynamics;
              trace_proj := fun _ => nil;
              initP := fun s => s = ∅ |};
      intros; eauto using crash_total_ok, crash_non_err_ok.
    - simpl; descend; unfold reads, puts; intuition eauto.
    - inversion 1; subst; simpl in *.
      (intuition eauto); propositional; discriminate.
  Defined.

End Log.
