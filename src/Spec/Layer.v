Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Abstraction.
Require Import Helpers.RelationAlgebra.
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
    refines absr (c_sem.(rexec) recover recover) (a_sem.(crash_step)).

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

  (* attempt to make rewriting across monad associativity a bit easier; instead
     of massaging the goal to have [r1] appear, instead generalize the
     hypothesis to apply to apply to [forall rx, r1; rx] *)
  Lemma impl_rx A B T (r1 r2: relation A B T) :
    r1 ---> r2 ->
    (forall C T2 (rx: T -> relation B C T2),
        and_then r1 rx ---> and_then r2 rx).
  Proof.
    intros.
    rel_congruence; auto.
  Qed.

  Tactic Notation "pose" "unfolded" constr(pf) tactic(t) :=
    let H := fresh in
    pose proof pf as H; t H; destruct_ands.

  Ltac unfold_refines pf :=
    let P := type of pf in
    let Psimpl := (eval unfold refines in P) in
            constr:(pf: Psimpl).

  Tactic Notation "rew" uconstr(pf) :=
    let pf' := (unfold_refines pf) in
        setoid_rewrite pf'; norm_goal.
  Tactic Notation "rew" "<-" uconstr(pf) :=
    let pf' := (unfold_refines pf) in
    setoid_rewrite <- pf'; norm_goal.
  Tactic Notation "rew" uconstr(pf) "in" ident(H) :=
    let pf' := (unfold_refines pf) in
        setoid_rewrite pf' in H at 1; norm_hyp H.
  Tactic Notation "rew" "<-" uconstr(pf) "in" ident(H) :=
    let pf' := (unfold_refines pf) in
        setoid_rewrite <- pf' in H at 1; norm_hyp H.

  Ltac Split := match goal with
                | |- (_ + _ ---> _) =>
                  apply rel_or_elim; norm
                | |- ?g ---> _ =>
                  match g with
                  | context[_ + _] =>
                    repeat (setoid_rewrite bind_dist_l ||
                            setoid_rewrite bind_dist_r);
                    apply rel_or_elim; norm
                  end
                end.

  Ltac Left := match goal with
               | |- _ ---> ?g =>
                 match g with
                 | context[_ + _] =>
                   rewrite <- rel_or_introl; norm
                 end
               end.

  Ltac Right := match goal with
               | |- _ ---> ?g =>
                 match g with
                 | context[_ + _] =>
                   rewrite <- rel_or_intror; norm
                 end
               end.

  Ltac left_associate H :=
    try rewrite <- ?bind_assoc in H;
    rewrite <- ?bind_assoc;
    repeat setoid_rewrite <- bind_assoc;
    try repeat setoid_rewrite <- bind_assoc in H.

  Tactic Notation "left" "assoc" "rew" constr(H) :=
    left_associate H;
    setoid_rewrite H;
    norm;
    norm_hyp H.

  Tactic Notation "left" "assoc" "rew" "<-" constr(H) :=
    left_associate H;
    setoid_rewrite <- H;
    norm;
    norm_hyp H.

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
      rew <- H.
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
    pose unfolded crash_step_refinement
         (fun H => unfold refines in H; rename H into Hcrash_step).
    induction rec; simpl; norm.
    - pose unfolded (rf.(compile_op_ok) op)
           (fun H => red in H; unfold rexec, refines in H).
      rew H0.
      Split.
      Left.
      Right.
    - auto.
    - repeat Split.
      + Left.
        Left.
        auto.
      + Left.
        Right.
        rew IHrec.
      + Right.
        pose unfolded (compile_exec_ok rec)
             (fun H => unfold refines in H).
        (* TODO: why does left assoc rew (compile_exec_ok rec) not work? *)
        left assoc rew H0.
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
    split; [ now apply compile_exec_ok | ].
    induction p; simpl; intros.
    - pose unfolded (rf.(compile_op_ok) op)
        (fun H => unfold compile_op_refines_step, crash_refines in H).
      match goal with
      | [ H: context[c_exec (compile_op _)] |- _ ] =>
        clear H (* normal execution of op is irrelevant *)
      end.
      unfold refines in *.
      unfold rexec in *; norm.
      setoid_rewrite exec_recover_bind.
      setoid_rewrite <- bind_assoc at 3.
      setoid_rewrite <- bind_assoc at 2.
      setoid_rewrite <- bind_assoc at 1.
      rewrite H0; norm.
      unfold exec_crash.
      setoid_rewrite <- bind_assoc at 3.
      setoid_rewrite bind_dist_r at 2; norm.
      rel_congruence.
      pose unfolded
           (compile_exec_ok rec)
           (fun H => unfold refines in H).

      (* TODO: proof about [rexec c_sem (compile rec) recover] *)


      admit.

    - let H := fresh "Hnoop" in
      pose proof (rf.(recovery_ok)) as H;
        unfold recovery_refines_noop, crash_refines in H;
        propositional.
      unfold rexec.
      unfold refines in *; norm.
      setoid_rewrite exec_crash_ret; norm.
      (* TODO: repeating a proof above about c_exec_recover of [recover;
        compile rec] *)
      setoid_rewrite exec_recover_bind.
      unfold rexec in H0.
  Abort.

End Layers.
