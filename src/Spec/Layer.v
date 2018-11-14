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
    initP: State -> Prop }.

Inductive InitStatus := Initialized | InitFailed.

(* LayerImpl is just the code needed to translate from one layer to another -
   the logical components are in [LayerRefinement] *)
Record LayerImpl C_Op Op :=
  { compile_op `(op: Op T) : proc C_Op T;
    (* TODO: layer implementations should be allowed to return from recovery
         (though it's unclear what purpose that would serve *)
    recover: proc C_Op unit;
    init: proc C_Op InitStatus; }.

Fixpoint compile Op C_Op `(impl: LayerImpl C_Op Op) T (p: proc Op T) : proc C_Op T :=
  match p with
  | Call op => impl.(compile_op) op
  | Ret v => Ret v
  | Bind p p' => Bind (impl.(compile) p) (fun v => impl.(compile) (p' v))
  end.

Fixpoint compile_seq Op C_Op `(impl: LayerImpl C_Op Op) R (p: proc_seq Op R) :
  proc_seq C_Op R :=
  match p with
  | Seq_Nil => Seq_Nil
  | Seq_Bind p p' => Seq_Bind (impl.(compile) p) (fun v => impl.(compile_seq) (p' v))
  end.

Definition compile_rec Op C_Op
           `(impl: LayerImpl C_Op Op)
           R (rec: proc Op R) : proc C_Op R :=
  Bind impl.(recover) (fun _ => impl.(compile) rec).

Definition initOutput {A} `(L: Layer Op) (r: relation (State L) (State L) A) (v : A) : Prop :=
  exists s1 s2, L.(initP) s1 /\ r s1 s2 v.

Hint Unfold refines : relation_rewriting.

Section Layers.

  Context C_Op (c_layer: Layer C_Op).
  Notation CState := c_layer.(State).
  Notation c_proc := (proc C_Op).
  Notation c_initP := c_layer.(initP).
  Notation c_sem := c_layer.(sem).
  Notation c_exec := c_layer.(sem).(exec).
  Notation c_exec_recover := c_layer.(sem).(exec_recover).
  Notation c_output := c_layer.(initOutput).

  Context Op (a_layer: Layer Op).
  Notation AState := a_layer.(State).
  Notation a_proc := (proc Op).
  Notation a_proc_seq := (proc_seq Op).
  Notation a_initP := a_layer.(initP).
  Notation a_sem := a_layer.(sem).
  Notation a_exec_recover := a_layer.(sem).(exec_recover).
  Notation a_output := a_layer.(initOutput).

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

  Definition recovery_refines_crash_step (impl: LayerImpl C_Op Op) (absr: relation AState CState unit) :=
    refines absr
            (c_sem.(crash_step);; c_exec_recover impl.(recover))
            (a_sem.(crash_step)).

  Record LayerRefinement :=
    { impl: LayerImpl C_Op Op;
      absr: relation AState CState unit;
      compile_op_ok : compile_op_refines_step impl absr;
      recovery_noop_ok : recovery_refines_crash_step impl absr;
      (* TODO: prove implementations are well-formed *)
      init_ok : test c_initP;; c_exec impl.(init) --->
                                                  (any (T:=unit);; test a_initP;; absr;; pure Initialized)
                (* failing initialization can do anything since a lower layer
                might have initialized before this failure *)
                + (any (T:=unit);; pure InitFailed)}.

  Context (rf: LayerRefinement).
  Notation compile_op := rf.(impl).(compile_op).
  Notation compile_rec := rf.(impl).(compile_rec).
  Notation compile_seq := rf.(impl).(compile_seq).
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
      left_assoc rew IHp.
      rel_congruence; norm.
      rew<- H.
  Qed.

  (* TODO: this is only for compatibility, get rid of it *)
  Theorem crash_step_refinement :
    refines rf.(absr) (c_sem.(crash_step);; c_exec_recover recover)
                      (a_sem.(crash_step)).
  Proof.
    exact rf.(recovery_noop_ok).
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
      + left_assoc rew (compile_exec_ok rec).
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
    left_assoc rew H.
    rel_congruence.
    rew compile_exec_ok.
  Qed.


  Lemma recover_ret R (rec: a_proc R) :
    refines rf.(absr)
                 (_ <- c_sem.(crash_step);
                    c_exec_recover (compile_rec rec))
                 (a_sem.(crash_step);; a_exec_recover rec).
  Proof.
    unfold refines.
    rew @exec_recover_bind.
    rew bind_star_unit.
    left_assoc rew crash_step_refinement.
    rel_congruence.
    rew rexec_star_rec.
  Qed.

  Theorem compile_rexec_ok T (p: a_proc T) R (rec: a_proc R) :
    refines rf.(absr)
                 (rexec c_sem (compile p) (compile_rec rec))
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
      left_assoc rew H0.
      rew bind_star_unit.

      rew rexec_star_rec.
      rewrite ?bind_dist_r; norm.
    - rew recover_ret.
    - repeat Split;
        [ Left; Left | Left; Right | Right ].
      + rew recover_ret.
      + rew IHp.
      + left_assoc rew compile_exec_ok.
        rel_congruence.
        rew H.
  Qed.

  Theorem compile_exec_seq_ok R (p: a_proc_seq R) (rec: a_proc R):
    refines rf.(absr)
                 (exec_seq c_sem (compile_seq p) (compile_rec rec))
                 (exec_seq a_sem p rec).
  Proof.
    unfold refines.
    induction p as [| ??? IH1]; do 2 rewrite exec_seq_unfold; simpl; [ norm |].
    repeat setoid_rewrite bind_dist_r. repeat setoid_rewrite bind_dist_l.
    eapply or_respects_impl.
    - left_assoc rew compile_exec_ok; repeat rel_congruence.
      left_assoc rew IH1.
    - left_assoc rew compile_rexec_ok; repeat rel_congruence.
      left_assoc rew IH1.
  Qed.

  Theorem compile_ok : forall T (p: a_proc T) R (rec: a_proc R),
        crash_refines
          rf.(absr) c_sem
                    (compile p) (compile_rec rec)
                    (a_sem.(exec) p)
                    (a_sem.(rexec) p rec).
  Proof.
    intros.
    split; [ now apply compile_exec_ok | now apply compile_rexec_ok ].
  Qed.

  Definition ifInit (inited:InitStatus) A `(r: relation A A T) :
    relation A A (option T) :=
    if inited
    then v <- r; pure (Some v)
    else pure None.

  Theorem complete_exec_ok : forall T (p: a_proc T),
      test c_initP;; inited <- c_exec rf.(impl).(init); ifInit inited (c_exec (compile p)) --->
           (any (T:=unit);; test a_initP;; v <- a_sem.(exec) p; any (T:=unit);; pure (Some v)) +
      (any (T:=unit);; pure None).
  Proof.
    intros.
    left_assoc rew rf.(init_ok).
    repeat rew bind_dist_r.
    simpl.
    Split.
    - Left.
      rel_congruence.
      rel_congruence.
      left_assoc rew (compile_exec_ok p).
      repeat rel_congruence.
      apply to_any.
    - Right.
  Qed.

  Theorem complete_rexec_ok : forall T (p: a_proc T) R (rec: a_proc R),
      test c_initP;; inited <- c_exec rf.(impl).(init); ifInit inited (c_sem.(rexec) (compile p) (compile_rec rec)) --->
           (any (T:=unit);; test a_initP;; v <- a_sem.(rexec) p rec; any (T:=unit);; pure (Some v)) +
      (any (T:=unit);; pure None).
  Proof.
    intros.
    left_assoc rew rf.(init_ok).
    repeat rew bind_dist_r.
    simpl.
    Split.
    - Left.
      rel_congruence.
      rel_congruence.
      left_assoc rew compile_rexec_ok.
      repeat rel_congruence.
      apply to_any.
    - Right.
  Qed.

  Theorem complete_exec_seq_ok : forall R (p: a_proc_seq R) (rec: a_proc R),
      test c_initP;; inited <- c_exec rf.(impl).(init); ifInit inited (c_sem.(exec_seq) (compile_seq p) (compile_rec rec)) --->
           (any (T:=unit);; test a_initP;; v <- a_sem.(exec_seq) p rec; any (T:=unit);; pure (Some v)) +
      (any (T:=unit);; pure None).
  Proof.
    intros.
    left_assoc rew rf.(init_ok).
    repeat rew bind_dist_r.
    simpl.
    Split.
    - Left.
      rel_congruence.
      rel_congruence.
      left_assoc rew compile_exec_seq_ok.
      repeat rel_congruence.
      apply to_any.
    - Right.
  Qed.

  (* State a version without test, with some defns unfolded *)
  Theorem complete_exec_seq_ok_alt R (p: a_proc_seq R) (rec: a_proc R)
      (cs1 cs2: CState) mv:
    c_initP cs1 ->
    (inited <- c_exec rf.(impl).(init);
     match inited with
     | InitFailed => pure None
     | Initialized =>
       v <- c_sem.(exec_seq) (compile_seq p) (compile_rec rec); pure (Some v)
     end) cs1 cs2 mv ->
    match mv with
    | None => True
    | Some v => exists as1 as2, a_initP as1 /\ (a_sem.(exec_seq) p rec) as1 as2 v
    end.
  Proof.
    intros.
    pose proof (complete_exec_seq_ok p rec).
    unfold ifInit in H1. edestruct (H1 cs1 cs2 mv).
    { exists tt, cs1. split; [firstorder|].
      destruct H0 as (i&cs1'&?&?).
      exists i, cs1'. split; intuition.
    }
    destruct H2 as ([]&as1&?&?).
    - edestruct H3 as ([]&?&((?&<-)&?)).
      destruct H5 as (v&as2&?&?&?&?&?).
      inversion H7; subst; exists as1, as2. subst; split; auto.
    - repeat destruct H2. inversion H3; subst; eauto.
  Qed.

  Theorem complete_exec_seq_ok_alt2 R (p: a_proc_seq R) (rec: a_proc R) v:
    c_output (inited <- c_exec rf.(impl).(init);
                match inited with
                | InitFailed => pure None
                | Initialized =>
                  v <- c_sem.(exec_seq) (compile_seq p) (compile_rec rec); pure (Some v)
                end) (Some v) ->
    a_output (a_sem.(exec_seq) p rec) v.
  Proof.
    unfold c_output, a_output. intros (s1&s2&?&?).
    eapply (complete_exec_seq_ok_alt) with (mv := Some v); eauto.
  Qed.

End Layers.

Coercion impl: LayerRefinement >-> LayerImpl.
Coercion sem : Layer >-> Dynamics.

Definition layer_impl_compose
           Op1 Op2 Op3
           (impl1: LayerImpl Op1 Op2)
           (impl2: LayerImpl Op2 Op3)
  : LayerImpl Op1 Op3.
Proof.
  refine {| compile_op T op :=
              impl1.(compile) (impl2.(compile_op) op);
            recover := Bind impl1.(recover)
                                    (fun (_:unit) =>
                                       impl1.(compile) impl2.(recover));
            init := Bind impl1.(init)
                                 (fun inited =>
                                    if inited
                                    then impl1.(compile) impl2.(init)
                                    else Ret InitFailed);
         |}.
Defined.

Definition layer_compose
           Op1 (l1: Layer Op1)
           Op2 (l2: Layer Op2)
           Op3 (l3: Layer Op3)
           (rf1: LayerRefinement l1 l2)
           (rf2: LayerRefinement l2 l3) :
  (* most abstract: l3  --+
                          | rf2
                    l2 <--+ ------+
                                  | rf1
     most concrete: l1 <----------+
   *)
  LayerRefinement l1 l3.
Proof.
  refine {| impl := layer_impl_compose rf1.(impl) rf2.(impl);
            absr := rf2.(absr);; rf1.(absr) |}.
    simpl; intros.
  - (* op crash refinement *)
    red; unfold layer_impl_compose; simpl.
    split; simpl; unfold refines; norm.
    + rew rf1.(compile_exec_ok).
      pose unfolded (rf2.(compile_op_ok) _ op)
           (fun H => hnf in H).
      left_assoc rew H.
    + rew rf1.(compile_rexec_ok).
      pose unfolded (rf2.(compile_op_ok) _ op)
           (fun H => hnf in H).
      left_assoc rew H0.
  - red; unfold refines, layer_impl_compose; simpl; norm.
    rew @exec_recover_bind.
    rew bind_star_unit.
    pose unfolded rf1.(crash_step_refinement)
                        (fun H => unfold refines in H).
    setoid_rewrite <- bind_assoc at 3.
    setoid_rewrite <- bind_assoc at 2.
    rew H.
    rew rf1.(rexec_star_rec).
    left_assoc rew rf2.(crash_step_refinement).
  - unfold layer_impl_compose; simpl.
    rewrite <- bind_assoc.
    rew rf1.(init_ok).
    Split.
    + rew rf1.(compile_exec_ok).
      setoid_rewrite <- bind_assoc at 2.
      rew rf2.(init_ok).
      repeat (setoid_rewrite bind_dist_r ||
              setoid_rewrite bind_dist_l); norm.
      left_assoc rew any_idem.
      Split.
      * Left.
      * Right.
        rewrite <- bind_assoc.
        rel_congruence.
        apply to_any.
    + Right.
Qed.
