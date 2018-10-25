Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Abstraction.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.Helpers.

Import RelationNotations.

Record Layer Op :=
  { State: Type;
    sem: Dynamics Op State;
    (* TODO: add init here *) }.

(* LayerImpl is just the code needed to translate from one layer to another -
   the logical components are in [LayerRefinement] *)
Record LayerImpl C_Op Op :=
  { compile_op `(op: Op T) : proc C_Op T;
    (* TODO: layer implementations should be allowed returning from recovery
         (though it's unclear what purpose that would serve *)
    recover: proc C_Op unit;
  (* TODO: add init here *) }.

Section Layers.

  Context C_Op (c_layer: Layer C_Op).
  Notation CState := c_layer.(State).
  Notation c_proc := (proc C_Op).
  Notation c_sem := c_layer.(sem).
  Notation c_exec_recover := c_layer.(sem).(exec_recover).

  Context Op (a_layer: Layer Op).
  Notation AState := a_layer.(State).
  Notation a_proc := (proc Op).
  Notation a_sem := a_layer.(sem).
  Notation a_exec_recover := a_layer.(sem).(exec_recover).

  Context (impl: LayerImpl C_Op Op).
  Notation compile_op := impl.(compile_op).
  Notation recover := impl.(recover).

  Definition compile_op_refines_step (absr: relation AState CState unit) :=
    forall T (op: Op T),
      crash_refines absr c_sem
                    (compile_op op) recover
                    (a_sem.(step) op)
                    (* same as [(pure tt + (a_sem.(step) op;; pure tt));;
                       a_sem.(crash_step)], but easier to write due to
                       parsing *)
                    (a_sem.(crash_step) +
                     (a_sem.(step) op;; a_sem.(crash_step))).

  Definition recovery_refines_noop (absr: relation AState CState unit) :=
    crash_refines absr c_sem
                  recover
                  recover
                  any (* normal behavior of recovery is irrelevant, we never ask
                  how it runs normally *)
                  (a_sem.(crash_step)).

  Record LayerRefinement :=
    { absr: relation AState CState unit;
      compile_op_ok : compile_op_refines_step absr;
      recovery_ok : recovery_refines_noop absr;
      (* TODO: init_ok *) }.

  Fixpoint compile T (p: a_proc T) : c_proc T :=
    match p with
    | Prim op => compile_op op
    | Ret v => Ret v
    | Bind p p' => Bind (compile p) (fun v => compile (p' v))
    end.

  Context (rf: LayerRefinement).

  (* need to mark things opaque since [setoid_rewrite] simplifies the goal
   (and we need [setoid_rewrite] to rewrite under bind binders) *)
  Opaque exec_recover.

  Theorem compile_ok : forall T (p: a_proc T) R (rec: a_proc R),
      crash_refines rf.(absr) c_sem
                    (compile p) (Bind recover (fun _ => compile rec))
                    (a_sem.(exec) p)
                    (a_sem.(rexec) p rec).
  Proof.
    induction p; simpl; intros.
    - let H := fresh "Hop_ok" in
      pose proof (rf.(compile_op_ok) op) as H;
        unfold compile_op_refines_step, crash_refines in H;
        propositional.
      split; eauto.
      unfold refines in *.
      unfold rexec in *; norm.
      setoid_rewrite exec_recover_bind.
      setoid_rewrite <- bind_assoc at 3.
      setoid_rewrite <- bind_assoc at 2.
      setoid_rewrite <- bind_assoc at 1.
      rewrite H0; norm.
      rewrite ?bind_dist_r; norm.
      apply rel_or_elim.
      + rewrite <- exec_crash_noop; norm.
        rel_congruence.
        admit.
      + unfold exec_crash.
        rewrite <- rel_or_intror; norm.
        rel_congruence.
        rel_congruence.
        admit.
    - let H := fresh "Hnoop" in
      pose proof (rf.(recovery_ok)) as H;
        unfold recovery_refines_noop, crash_refines in H;
        propositional.
      split; simpl.
      + unfold refines; norm.
      + unfold refines in *; norm.
        rewrite <- exec_crash_noop; norm.
        (* TODO: repeating a proof above about c_exec_recover of [recover;
        compile rec] *)
        setoid_rewrite exec_recover_bind.
        unfold rexec in H0.
  Abort.

End Layers.
