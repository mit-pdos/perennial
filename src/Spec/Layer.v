Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Abstraction.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
Require Import Tactical.ProofAutomation.

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

Fixpoint compile Op C_Op `(impl: LayerImpl C_Op Op) T (p: proc Op T) : proc C_Op T :=
  match p with
  | Prim op => impl.(compile_op) op
  | Ret v => Ret v
  | Bind p p' => Bind (impl.(compile) p) (fun v => impl.(compile) (p' v))
  end.

Hint Unfold refines : relation_rewriting.

Section Layers.

  Context C_Op (c_layer: Layer C_Op).
  Notation CState := c_layer.(State).
  Notation c_proc := (proc C_Op).
  Notation c_sem := c_layer.(sem).
  Notation c_exec := c_layer.(sem).(exec).
  Notation c_exec_recover := c_layer.(sem).(exec_recover).

  Context Op (a_layer: Layer Op).
  Notation AState := a_layer.(State).
  Notation a_proc := (proc Op).
  Notation a_sem := a_layer.(sem).
  Notation a_exec_recover := a_layer.(sem).(exec_recover).

  Definition compile_op_refines_step (impl: LayerImpl C_Op Op) (absr: relation AState CState unit) :=
    forall T (op: Op T),
      crash_refines absr c_sem
                    (impl.(compile_op) op) impl.(recover)
                    (a_sem.(step) op)
                    (* same as [(pure tt + (a_sem.(step) op;; pure tt));;
                       a_sem.(crash_step)], but easier to write due to
                       parsing *)
                    (a_sem.(crash_step) +
                     (a_sem.(step) op;; a_sem.(crash_step))).

  Definition recovery_refines_noop (impl: LayerImpl C_Op Op) (absr: relation AState CState unit) :=
    refines absr
            (c_sem.(rexec) impl.(recover) impl.(recover))
            (a_sem.(crash_step)).

  Record LayerRefinement :=
    {
      impl: LayerImpl C_Op Op;
      absr: relation AState CState unit;
      compile_op_ok : compile_op_refines_step impl absr;
      recovery_ok : recovery_refines_noop impl absr;
      (* TODO: init_ok *) }.

  Context (rf: LayerRefinement).
  Notation compile_op := rf.(impl).(compile_op).
  Notation compile := rf.(impl).(compile).
  Notation recover := rf.(impl).(recover).

  (* need to mark things opaque since [setoid_rewrite] simplifies the goal
   (and we need [setoid_rewrite] to rewrite under bind binders) *)
  Opaque exec_recover.

  Theorem compile_exec_ok : forall T (p: a_proc T),
      refines
        rf.(absr)
             (c_exec (compile p))
             (a_sem.(exec) p).
  Proof.
    induction p; simpl; intros.
    - pose unfolded (rf.(compile_op_ok) op)
           (fun H => hnf in H).
      propositional.
    - unfold refines; norm.
    - unfold refines in *; norm.
      left assoc rew IHp.
      rel_congruence; norm.
      rew<- H.
  Qed.

  Theorem crash_step_refinement :
    refines rf.(absr) (c_sem.(crash_step);; c_exec_recover recover)
                      (a_sem.(crash_step)).
  Proof.
    unfold refines.
    pose unfolded (rf.(recovery_ok))
         (fun H => red in H; unfold rexec, refines in H).
    rew <- exec_crash_noop in H.
    assumption.
  Qed.

  Theorem rexec_rec R (rec: a_proc R):
    refines rf.(absr)
                 (c_sem.(rexec) (compile rec) recover)
                 (a_sem.(exec_crash) rec;; a_sem.(crash_step)).
  Proof.
    unfold refines, rexec.
    induction rec; simpl; norm.
    - pose unfolded (rf.(compile_op_ok) op)
           (fun H => red in H; unfold rexec, refines in H).
      rew H0.
      Split.
      Left.
      Right.
    - rew crash_step_refinement.
    - repeat Split; [ Left; Left | Left; Right | Right ].
      + rew crash_step_refinement.
      + rew IHrec.
      + left assoc rew (compile_exec_ok rec).
        rew H.
  Qed.

  Theorem rexec_star_rec R (rec: a_proc R) :
    refines rf.(absr)
                 (seq_star (rexec c_sem (compile rec) recover);; c_exec (compile rec))
                 (a_exec_recover rec).
  Proof.
    unfold refines.
    rew @exec_recover_unfold.
    pose unfolded (rexec_rec rec)
         (fun H => red in H).
    apply simulation_seq_value in H.
    left assoc rew H.
    rel_congruence.
    rew compile_exec_ok.
  Qed.

  Lemma recover_ret R (rec: a_proc R) :
    refines rf.(absr)
                 (_ <- c_sem.(crash_step);
                    c_exec_recover (Bind recover (fun _ => compile rec)))
                 (a_sem.(crash_step);; a_exec_recover rec).
  Proof.
    unfold refines.
    rew @exec_recover_bind.
    rew bind_star_unit.
    pose proof crash_step_refinement.
    unfold refines in H.
    left assoc rew crash_step_refinement.
    rel_congruence.
    rew rexec_star_rec.
  Qed.

  Theorem compile_rexec_ok T (p: a_proc T) R (rec: a_proc R) :
    refines rf.(absr)
                 (rexec c_sem (compile p)
                        (Bind recover (fun _ => compile rec)))
                 (rexec a_sem p rec).
  Proof.
    unfold refines, rexec.
    induction p; simpl; norm.
    - pose unfolded (rf.(compile_op_ok) op)
        (fun H => hnf in H; unfold rexec, refines in H).
      match goal with
      | [ H: context[c_exec (compile_op _)] |- _ ] =>
        clear H (* normal execution of op is irrelevant *)
      end.
      rew @exec_recover_bind.
      left assoc rew H0.
      rew bind_star_unit.

      rew rexec_star_rec.
      rewrite ?bind_dist_r; norm.
    - rew recover_ret.
    - repeat Split;
        [ Left; Left | Left; Right | Right ].
      + rew recover_ret.
      + rew IHp.
      + left assoc rew compile_exec_ok.
        rel_congruence.
        rew H.
  Qed.

  Theorem compile_ok : forall T (p: a_proc T) R (rec: a_proc R),
        crash_refines
          rf.(absr) c_sem
                    (compile p) (Bind recover (fun _ => compile rec))
                    (a_sem.(exec) p)
                    (a_sem.(rexec) p rec).
  Proof.
    intros.
    split; [ now apply compile_exec_ok | now apply compile_rexec_ok ].
  Qed.

End Layers.
