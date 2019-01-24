Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Abstraction.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
Require Import Helpers.RelationTheorems.
Require Import Tactical.ProofAutomation.

Import RelationNotations.
Require FunctionalExtensionality.

Record Layer Op :=
  { State: Type;
    sem: Dynamics Op State;
    (* TODO: should these be part of Dynamics instead of Layer? *)
    trace_proj: State -> list Event;
    crash_preserves_trace:
      forall s1 s2, sem.(crash_step) s1 (Val s2 tt) -> trace_proj s1 = trace_proj s2;
    crash_total: forall s1, exists s2, sem.(crash_step) s1 (Val s2 tt);
    crash_non_err: forall s1 ret, sem.(crash_step) s1 ret -> ret <> Err;
    initP: State -> Prop }.

Inductive InitStatus := Initialized | InitFailed.

(* LayerImpl is just the code needed to translate from one layer to another -
   the logical components are in [LayerRefinement] *)
Record LayerImpl C_Op Op :=
  { compile_op `(op: Op T) : proc C_Op T;
    (* TODO: layer implementations should be allowed to return from recovery
         (though it's unclear what purpose that would serve *)
    recover: rec_seq C_Op;
    (* init: proc C_Op InitStatus; *) }.

Fixpoint compile Op C_Op `(impl: LayerImpl C_Op Op) T (p: proc Op T) : proc C_Op T :=
  match p with
  | Call op => impl.(compile_op) op
  | Ret v => Ret v
  | Bind p p' => Bind (impl.(compile) p) (fun v => impl.(compile) (p' v))
  | Loop b init => Loop (fun mt => impl.(compile) (b mt)) init
  | Spawn p => Spawn (impl.(compile) p)
  end.

Fixpoint compile_seq Op C_Op `(impl: LayerImpl C_Op Op) (ps: rec_seq Op) :
  rec_seq C_Op :=
  match ps with
  | Seq_Nil => Seq_Nil
  | Seq_Cons p ps' => Seq_Cons (impl.(compile) p) (impl.(compile_seq) ps')
  end.

Definition compile_rec Op C_Op `(impl: LayerImpl C_Op Op) (rec: rec_seq Op) : rec_seq C_Op :=
  rec_seq_append impl.(recover) (impl.(compile_seq) rec).

Definition initOutput {A} `(L: Layer Op) (r: relation (State L) (State L) A) (v : A) : Prop :=
  exists s1 s2, L.(initP) s1 /\ r s1 (Val s2 v).

Hint Unfold refines : relation_rewriting.

Section Layers.

  Context C_Op (c_layer: Layer C_Op).
  Notation CState := c_layer.(State).
  Notation c_proc := (proc C_Op).
  Notation c_initP := c_layer.(initP).
  Notation c_sem := c_layer.(sem).
  Notation c_trace_proj := c_layer.(trace_proj).
  Notation c_exec := c_layer.(sem).(exec).
  Notation c_exec_partial := c_layer.(sem).(exec_partial).
  Notation c_rexec_partial := c_layer.(sem).(rexec_partial).
  Notation c_exec_seq := c_layer.(sem).(exec_seq).
  Notation c_exec_seq_partial := c_layer.(sem).(exec_seq_partial).
  Notation c_rexec_seq_partial := c_layer.(sem).(rexec_seq_partial).
  Notation c_exec_recover := c_layer.(sem).(exec_recover).
  Notation c_exec_recover_partial := c_layer.(sem).(exec_recover_partial).
  Notation c_exec_recover1 := c_layer.(sem).(exec_recover1).
  Notation c_output := c_layer.(initOutput).

  Context Op (a_layer: Layer Op).
  Notation AState := a_layer.(State).
  Notation a_proc := (proc Op).
  Notation a_rec_seq := (rec_seq Op).
  Notation a_initP := a_layer.(initP).
  Notation a_sem := a_layer.(sem).
  Notation a_trace_proj := a_layer.(trace_proj).
  Notation a_exec := a_layer.(sem).(exec).
  Notation a_exec_partial := a_layer.(sem).(exec_partial).
  Notation a_exec_halt := a_layer.(sem).(exec_halt).
  Notation a_exec_recover := a_layer.(sem).(exec_recover).
  Notation a_exec_recover1 := a_layer.(sem).(exec_recover1).
  Notation a_output := a_layer.(initOutput).

  Definition compile_refines (impl: LayerImpl C_Op Op) (absr: relation AState CState unit) :=
    forall T (p: proc Op T),
      crash_refines absr c_sem
                    (impl.(compile) p) impl.(recover)
                    (a_exec p)
                    (a_exec_halt p;; a_sem.(crash_step)).

  Definition trace_relation : relation AState CState unit :=
    fun sa ret => exists sc, ret = Val sc tt /\ a_trace_proj sa = c_trace_proj sc.

  Definition trace_refines (impl: LayerImpl C_Op Op) (absr: relation AState CState unit) :=
    forall T (p: proc Op T),
      halt_refines absr c_sem trace_relation
                    (impl.(compile) p) impl.(recover)
                    (a_exec_halt p)
                    (a_exec_halt p;; a_sem.(crash_step)).

  (* I don't think we can so simply phrase things in terms of per-op correctness, without
     baking in too strongly how the reasoning is to be done *)

  (*
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
   *)

  Definition recovery_refines_crash_step (impl: LayerImpl C_Op Op) (absr: relation AState CState unit) :=
    refines absr
            (c_sem.(crash_step);; c_exec_recover impl.(recover))
            (a_sem.(crash_step)).

  Definition recovery_refines_crash_step_trace (impl: LayerImpl C_Op Op) (absr: relation AState CState unit) :=
    refines_if absr trace_relation
            (c_sem.(crash_step);; c_exec_recover_partial impl.(recover))
            (a_sem.(crash_step)).

  Record LayerRefinement :=
    { impl: LayerImpl C_Op Op;
      absr: relation AState CState unit;
      compile_ok : compile_refines impl absr;
      trace_ok : trace_refines impl absr;
      absr_preserves_trace: absr ---> trace_relation
      (* TODO: prove implementations are well-formed *)
      (*
      init_ok : test c_initP;; c_exec impl.(init) --->
                                                  (any (T:=unit);; test a_initP;; absr;; pure (existT _ _ Initialized))
                (* failing initialization can do anything since a lower layer
                might have initialized before this failure *)
                + (any (T:=unit);; pure (existT _ _ InitFailed))
     *)
    }.

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
  Proof. intros. eapply (rf.(compile_ok) p); eauto. Qed.

  Theorem compile_seq_exec_ok : forall (p: a_rec_seq),
      refines
        rf.(absr)
             (c_exec_seq (compile_seq p))
             (a_sem.(exec_seq) p).
  Proof.
    unfold refines; induction p.
    - simpl; norm.
    - simpl.
      pose unfolded (rf.(compile_ok) p)
           (fun H => red in H; unfold rexec, refines in H).
      rewrite <-bind_assoc. rewrite H.
      repeat rewrite bind_assoc.
      rel_congruence.
      repeat rewrite bind_assoc.
      rew bind_left_id. eauto.
  Qed.

  Theorem compile_seq_trace_ok1 : forall (p: a_rec_seq),
      refines_if rf.(absr) trace_relation
             (c_exec_seq_partial (compile_seq p))
             (a_sem.(exec_seq_partial) p).
  Proof.
    unfold refines_if; induction p.
    - simpl; norm. setoid_rewrite rf.(absr_preserves_trace); reflexivity.
    - simpl.
      pose unfolded (rf.(compile_ok) p)
           (fun H => red in H; unfold rexec, refines in H).
      Split.
      * rewrite <-bind_assoc. rewrite H.
        Left.
        repeat rewrite bind_assoc.
        rel_congruence.
        repeat rewrite bind_assoc.
        rew bind_left_id. eauto.
      * Right.
        pose unfolded (rf.(trace_ok) p)
             (fun H => red in H; unfold rexec, refines_if, exec_halt in H).
        rew H1.
  Qed.

  Lemma recovery_noop_ok : recovery_refines_crash_step rf.(impl) rf.(absr).
  Proof.
    unfold recovery_refines_crash_step, refines.
    pose unfolded (rf.(compile_ok) (Ret tt)) (fun H => red in H; unfold refines in H).
    simpl in *.
    unfold rexec in H0.
    setoid_rewrite exec_partial_ret in H0.
    unfold a_exec_halt in H0.
    setoid_rewrite exec_partial_ret in H0.
    setoid_rewrite bind_left_id in H0.
    setoid_rewrite bind_left_id in H0.
    eauto.
  Qed.

  Lemma recovery_noop_trace_ok : recovery_refines_crash_step_trace rf.(impl) rf.(absr).
  Proof.
    unfold recovery_refines_crash_step_trace, refines_if.
    pose unfolded (rf.(trace_ok) (Ret tt)) (fun H => red in H; unfold refines_if in H).
    simpl in *.
    unfold rexec_partial in H0.
    setoid_rewrite exec_partial_ret in H0.
    unfold a_exec_halt in H0.
    setoid_rewrite exec_partial_ret in H0.
    setoid_rewrite bind_left_id in H0.
    setoid_rewrite bind_left_id in H0.
    eauto.
  Qed.

  Theorem compile_seq_trace_ok2 : forall (p: a_rec_seq),
      refines_if rf.(absr) trace_relation
             (c_rexec_seq_partial (compile_seq p) recover)
             (a_sem.(exec_seq_partial) p;; a_sem.(crash_step)).
  Proof.
    unfold refines_if; induction p.
    - simpl; norm. eapply recovery_noop_trace_ok.
    - simpl. unfold rexec_seq_partial.
      simpl.
      Split;
      pose unfolded (rf.(compile_ok) p)
           (fun H => red in H; unfold rexec, refines in H).
      * rewrite <-bind_assoc. rewrite H.
        Left.
        repeat rewrite bind_assoc.
        rel_congruence.
        repeat rewrite bind_assoc.
        rew bind_left_id. rew IHp.
      * Right.
        pose unfolded (rf.(trace_ok) p)
             (fun H => red in H; unfold rexec, refines_if, exec_halt in H).
        rew H2.
  Qed.

  Lemma absr_preserves_trace' s1 s2:
    rf.(absr) s1 (Val s2 tt) -> trace_proj _ s1 = trace_proj _ s2.
  Proof.
    intros. edestruct absr_preserves_trace; eauto;
    inversion H0; intuition; congruence.
  Qed.

  Lemma absr_no_err sa:
    rf.(absr) sa Err -> False.
  Proof.
    intros. edestruct absr_preserves_trace; eauto;
    inversion H0; intuition; congruence.
  Qed.

  (* TODO: this is only for compatibility, get rid of it *)
  Theorem crash_step_refinement :
    refines rf.(absr) (c_sem.(crash_step);; c_exec_recover recover)
                      (a_sem.(crash_step)).
  Proof. exact (recovery_noop_ok). Qed.

  Theorem rexec_seq_rec (rec: a_rec_seq):
    refines rf.(absr)
                 (c_sem.(rexec_seq) (compile_seq rec) recover)
                 (a_sem.(exec_seq_partial) rec;; a_sem.(crash_step)).
  Proof.
    unfold refines, rexec.
    induction rec; simpl; norm.
    - apply crash_step_refinement.
    - rewrite rexec_seq_unfold. simpl.
      rew bind_dist_r.
      rew bind_dist_l.
      Split.
      * pose unfolded (rf.(compile_ok) p)
           (fun H => red in H; unfold rexec, refines in H).
        rewrite <-bind_assoc. rewrite H.
        Left.
        repeat rewrite bind_assoc.
        rel_congruence.
        repeat rewrite bind_assoc.
        setoid_rewrite bind_left_id.
        rewrite IHrec.
        repeat rewrite bind_assoc.
        rel_congruence.
      * pose unfolded (rf.(compile_ok) p)
           (fun H => red in H; unfold rexec, refines in H).
        rewrite <-bind_assoc.
        Right.
        repeat setoid_rewrite bind_assoc in H0.
        rewrite bind_assoc.
        setoid_rewrite bind_left_id in H0.
        rew H0.
  Qed.

  Theorem rexec_star_rec (rec: a_rec_seq) :
    refines rf.(absr)
                 (seq_star (rexec_seq c_sem (compile_seq rec) recover);; c_exec_seq (compile_seq rec))
                 (a_exec_recover rec).
  Proof.
    unfold refines.
    rew @exec_recover_unfold.
    pose unfolded (rexec_seq_rec rec)
         (fun H => red in H).
    apply simulation_seq_value_no_err in H; eauto using absr_no_err.
    { left_assoc rew H.
      rel_congruence.
      rew compile_seq_exec_ok. }
  Qed.

  Lemma recover_ret (rec: a_rec_seq) :
    refines rf.(absr)
                 (_ <- c_sem.(crash_step);
                    c_exec_recover (compile_rec rec))
                 (a_sem.(crash_step);; a_exec_recover rec).
  Proof.
    unfold refines.
    rew @exec_recover_append.
    left_assoc rew crash_step_refinement.
    rel_congruence.
    rew rexec_star_rec.
  Qed.

  Theorem compile_rexec_ok T (p: a_proc T) (rec: a_rec_seq) :
    refines rf.(absr)
                 (rexec c_sem (compile p) (compile_rec rec))
                 (rexec a_sem p rec).
  Proof.
    unfold refines, rexec.
    pose unfolded (rf.(compile_ok) p)
         (fun H => red in H; unfold rexec, refines in H).
    rew @exec_recover_append.
    left_assoc rew H0.
    rel_congruence.
    rew rexec_star_rec.
  Qed.

  Lemma crash_trace_relation : (a_sem.(crash_step);; trace_relation) <---> trace_relation.
  Proof.
    split.
    - intros sa [? []|].
      * intros ([]&sa'&Hcrash&Hrel).
        right. destruct Hrel as (sc&Hinv&?). inversion Hinv. subst.
        eexists; split; eauto.
        transitivity (trace_proj _ sa'); eauto.
        eapply crash_preserves_trace; eauto.
      * intros [Hhd|(?&?&?&(?&?&?))].
        { exfalso. eapply crash_non_err; eauto. }
        congruence.
    - intros sa [? []|] H.
      * destruct (crash_total _ sa) as (sa'&?).
        right. exists tt, sa'; split; eauto.
        eexists; split; eauto. transitivity (trace_proj _ sa); eauto.
        { symmetry. eapply crash_preserves_trace; eauto. }
        destruct H as (?&?&?). congruence.
      * destruct H as (?&?&?). congruence.
  Qed.

  Lemma crash_trace_relation' :
    (a_sem.(crash_step);; trace_relation;; pure tt) <---> (trace_relation;; pure tt).
  Proof.
    rewrite <-bind_assoc.
    rewrite crash_trace_relation; reflexivity.
  Qed.

  (* Under the assumption that crash steps preserve traces, the first conjunct of
     halt_refines is redundant for trace relation *)
  Lemma halt_refines_trace_relation_alt {T} (absr: relation AState CState unit)
        (pc: c_proc T) (p: a_proc T) rec :
    (forall sa, absr sa Err -> False) ->
    refines_if absr trace_relation (c_rexec_partial pc rec)
                    (a_exec_halt p;; a_sem.(crash_step)) ->
    halt_refines absr c_sem trace_relation pc rec
                 (a_exec_halt p)
                 (a_exec_halt p;; a_sem.(crash_step)).
  Proof.
    intros Habsr_err.
    unfold halt_refines, refines_if; intros Href; split; auto.
    unfold rexec_partial in Href.
    rew<- crash_trace_relation.
    setoid_rewrite bind_assoc in Href.
    setoid_rewrite <-exec_recover_partial_noop in Href.
    setoid_rewrite bind_unit' in Href.
    unfold a_exec_halt in Href.
    setoid_rewrite bind_assoc in Href.
    setoid_rewrite bind_left_id in Href.
    setoid_rewrite crash_trace_relation'.
    setoid_rewrite crash_trace_relation' in Href.
    setoid_rewrite bind_right_id_unit in Href.
    setoid_rewrite bind_right_id_unit.
    intros sA [sC' []|].
    * intros ([]&sC&Habsr&Hexec_halt).
      destruct Hexec_halt as (?&?&?&Hpure); subst.
      inversion Hpure; subst.
      edestruct (crash_total _ sC') as (sC''&Hcrash).
      edestruct (Href sA (Val sC'' tt)) as [?|Hv]; eauto. (* [(sA'&?&?&Htrace)|]. *)
      {
        do 2 eexists; split; eauto.
        do 2 eexists; split; eauto.
      }
      destruct Hv as (sA'&?&?&Htrace).
      right.
      do 3 eexists; eauto.
      apply crash_preserves_trace in Hcrash.
      eexists; split; eauto.
      transitivity (c_trace_proj sC''); eauto.
      destruct Htrace as (?&Hinv&?). inversion Hinv; subst; eauto.
    * intros [| ([]&sC&Habsr&Hexec_halt)].
      { exfalso; eauto. }
      destruct Hexec_halt as [?|(?&?&?&Hpure)]; subst.
      ** edestruct (Href sA Err) as [?|Hv]; eauto. (* [(sA'&?&?&Htrace)|]. *)
          right.
          do 2 eexists; split; eauto.
          left; eauto.
      ** inversion Hpure.
  Qed.

  Theorem compile_rexec_trace_ok T (p: a_proc T) (rec: a_rec_seq) :
    refines_if rf.(absr) trace_relation
                 (rexec_partial c_sem (compile p) (compile_rec rec))
                 (rexec_partial a_sem p rec).
  Proof.
    unfold refines_if, rexec_partial.
    pose unfolded (rf.(trace_ok) p)
         (fun H => red in H; unfold rexec_partial, refines_if in H).
    rew @exec_recover_partial_append.
    Split; [Split|].
    - left_assoc rew H0.
      rel_congruence.
      setoid_rewrite <-(exec_seq_partial_noop a_sem rec) at 2.
      setoid_rewrite <-(seq_star_none).
      rew bind_unit.
    (* TODO: next two cases have redundancy *)
    - pose unfolded (compile_rexec_ok p rec)
         (fun H => red in H; unfold rexec, refines in H).
      unfold compile_rec in H1.
      setoid_rewrite exec_recover_append in H1.
      pose unfolded (rf.(compile_ok) p)
           (fun H => red in H; unfold rexec, refines in H).
      left_assoc rew H3.
      do 2 rel_congruence.
      pose unfolded (rexec_seq_rec rec)
         (fun H => red in H; unfold rexec, rexec_seq, refines in H).
      apply simulation_seq_value_no_err in H4; eauto using absr_no_err.
      left_assoc rew H4.
      rel_congruence.
      pose unfolded (compile_seq_trace_ok2 rec)
         (fun H => red in H; unfold rexec, rexec_seq, refines in H).
      left_assoc rew H5.
      rel_congruence.
      rewrite bind_unit.
      match goal with | [ H : unit |- _] => destruct H end.
      left_assoc rew crash_trace_relation.
    - pose unfolded (compile_rexec_ok p rec)
         (fun H => red in H; unfold rexec, refines in H).
      unfold compile_rec in H1.
      setoid_rewrite exec_recover_append in H1.
      pose unfolded (rf.(compile_ok) p)
           (fun H => red in H; unfold rexec, refines in H).
      left_assoc rew H3.
      do 2 rel_congruence.
      pose unfolded (rexec_seq_rec rec)
         (fun H => red in H; unfold rexec, rexec_seq, refines in H).
      apply simulation_seq_value_no_err in H4; eauto using absr_no_err.
      left_assoc rew H4.
      rel_congruence.
      pose unfolded (compile_seq_trace_ok1 rec)
         (fun H => red in H; unfold rexec, rexec_seq, refines in H).
      left_assoc rew H5.
  Qed.

  (*
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
   *)

  Theorem compile_ok' : forall T (p: a_proc T) rec,
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

  (*
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

  Theorem complete_exec_seq_ok_tests : forall R (p: a_proc_seq R) (rec: a_proc R),
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
   *)

  (* State a version without test, with some defns unfolded *)
  (*
  Theorem complete_exec_seq_ok_unfolded R (p: a_proc_seq R) (rec: a_proc R)
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
    pose proof (complete_exec_seq_ok_tests p rec).
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

  Theorem complete_exec_seq_ok R (p: a_proc_seq R) (rec: a_proc R) v:
    c_output (inited <- c_exec rf.(impl).(init);
                match inited with
                | InitFailed => pure None
                | Initialized =>
                  v <- c_sem.(exec_seq) (compile_seq p) (compile_rec rec); pure (Some v)
                end) (Some v) ->
    a_output (a_sem.(exec_seq) p rec) v.
  Proof.
    unfold c_output, a_output. intros (s1&s2&?&?).
    eapply (complete_exec_seq_ok_unfolded) with (mv := Some v); eauto.
  Qed.
   *)

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
            recover := rec_seq_append impl1.(recover) (impl1.(compile_seq) impl2.(recover));
            (*
            init := Bind impl1.(init)
                                 (fun inited =>
                                    if inited
                                    then impl1.(compile) impl2.(init)
                                    else Ret InitFailed);
             *)
         |}.
Defined.

(* TODO: the use of fun ext here is not necessary. *)
Lemma compose_compile_equiv:
forall (Op1 : Type -> Type) (l1 : Layer Op1) (Op2 : Type -> Type)
  (l2 : Layer Op2) (Op3 : Type -> Type) (l3 : Layer Op3)
  (rf1 : LayerRefinement l1 l2) (rf2 : LayerRefinement l2 l3) T (p: proc Op3 T),
  exec_equiv (sem l1) (compile (layer_impl_compose rf1 rf2) p) (compile rf1 (compile rf2 p)).
Proof.
  intros Op1 l1 Op2 l2 Op3 l3 rf1 rf2 T p.
  cut (compile (layer_impl_compose rf1 rf2) p =
       (compile rf1 (compile rf2 p))).
  { intros ->. reflexivity. }
  induction p; simpl; eauto; try congruence.
  - f_equal; eauto.
    apply FunctionalExtensionality.functional_extensionality; eauto.
  - f_equal; eauto.
    apply FunctionalExtensionality.functional_extensionality; eauto.
Qed.

Lemma compose_compile_op:
  forall (Op1 : Type -> Type) (l1 : Layer Op1) (Op2 : Type -> Type)
    (l2 : Layer Op2) (Op3 : Type -> Type) (l3 : Layer Op3)
    (rf1 : LayerRefinement l1 l2) (rf2 : LayerRefinement l2 l3),
    compile_refines l1 l3 (layer_impl_compose rf1 rf2)
                            (_ <- rf2.(absr); rf1.(absr)).
Proof.
  intros Op1 l1 Op2 l2 Op3 l3 rf1 rf2 T p.
  red. simpl.
  split; simpl; norm; unfold refines; setoid_rewrite compose_compile_equiv at 1.
  - rew bind_assoc.
    rew rf1.(compile_exec_ok).
    pose unfolded (rf2.(compile_ok) p)
         (fun H => hnf in H).
    left_assoc rew H.
  - rew bind_assoc.
    rew rf1.(compile_rexec_ok).
    pose unfolded (rf2.(compile_ok) p)
         (fun H => hnf in H).
    left_assoc rew H0.
Qed.

Lemma trace_relation_trans:
  forall (Op1 : Type -> Type) (l1 : Layer Op1) (Op2 : Type -> Type)
    (l2 : Layer Op2) (Op3 : Type -> Type) (l3 : Layer Op3),
  (trace_relation l2 l3;; trace_relation l1 l2) --->
  trace_relation l1 l3.
Proof.
  intros. intros s3 [s1 []|].
  * intros ([]&s2&?&?). right.
    destruct H.
    destruct H0. intuition. eexists; split; eauto; congruence.
  * intros [H|(?&?&?&Hp)].
    ** inversion H; intuition; congruence.
    ** inversion Hp; intuition; congruence.
Qed.

Lemma compile_trace_absr:
  forall (Op1 : Type -> Type) (l1 : Layer Op1) (Op2 : Type -> Type)
    (l2 : Layer Op2) (Op3 : Type -> Type) (l3 : Layer Op3)
    (rf1 : LayerRefinement l1 l2) (rf2 : LayerRefinement l2 l3),
    trace_refines l1 l3 (layer_impl_compose rf1 rf2)
                                (_ <- rf2.(absr); rf1.(absr)).
Proof.
  intros Op1 l1 Op2 l2 Op3 l3 rf1 rf2 T p.
  red. simpl.
  split; simpl; norm; unfold refines_if; setoid_rewrite compose_compile_equiv at 1.
  - rew bind_assoc.
    edestruct rf1.(trace_ok) as (Ht1&_). unfold refines_if in Ht1.
    rew Ht1.
    edestruct rf2.(trace_ok) as (Ht2&_). unfold refines_if in Ht2.
    left_assoc rew Ht2.
    rel_congruence.
    left_assoc rew trace_relation_trans.
  - rew bind_assoc.
    pose unfolded (rf1.(compile_rexec_trace_ok) (compile rf2 p) (rf2.(recover)))
        (fun H => unfold refines_if, compile_rec in H).
    rew H.
    edestruct rf2.(trace_ok) as (_&Ht2). unfold refines_if in Ht2.
    left_assoc rew Ht2.
    rel_congruence.
    rel_congruence.
    left_assoc rew trace_relation_trans.
Qed.

(*
Lemma compile_init_ok:
  forall (Op1 : Type -> Type) (l1 : Layer Op1) (Op2 : Type -> Type)
    (l2 : Layer Op2) (Op3 : Type -> Type) (l3 : Layer Op3)
    (rf1 : LayerRefinement l1 l2) (rf2 : LayerRefinement l2 l3),
    _ <- test l1.(initP);
      exec l1 (layer_impl_compose rf1 rf2).(init)
                                             --->
                                             (_ <- any (T:=unit); _ <- test l3.(initP); _ <- _ <- rf2.(absr);
                                                rf1.(absr);
                                                pure Initialized) + (_ <- any (T:=unit); pure InitFailed).
Proof.
  intros Op1 l1 Op2 l2 Op3 l3 rf1 rf2.
  unfold layer_impl_compose; simpl.
  rewrite <- bind_assoc.
  rew rf1.(init_ok).
  Split.
  - rew rf1.(compile_exec_ok).
    setoid_rewrite <- bind_assoc at 2.
    rew rf2.(init_ok).
    repeat (setoid_rewrite bind_dist_r ||
            setoid_rewrite bind_dist_l); norm.
    left_assoc rew any_idem.
    Split.
    + Left.
    + Right.
      rewrite <- bind_assoc.
      rel_congruence.
      apply to_any.
  - Right.
Qed.
*)


Definition refinement_transitive
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
  - apply compose_compile_op.
  - apply compile_trace_absr.
  - intros s3 [s1 []|].
    * intros ([]&s2&?&?).
      right. eexists; split; eauto. transitivity (l2.(trace_proj) s2);
      eapply absr_preserves_trace'; eauto.
    * intros [?|(?&?&?&?)]; exfalso;
      eapply absr_no_err; eauto.
Qed.
