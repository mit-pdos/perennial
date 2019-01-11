From Tactical Require Import Propositional.

Require Import Spec.Proc.

Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
Require Import Helpers.RelationTheorems.

Import RelationNotations.

Section Abstraction.
  Context (AState CState:Type).
  Context (absr: relation AState CState unit).

  Definition refines T
             (p: relation CState CState T)
             (spec: relation AState AState T) :=
    (absr;; p) ---> (v <- spec; absr;; pure v).

  Definition refines_if T
             (r: relation AState CState unit)
             (p: relation CState CState T)
             (spec: relation AState AState T) :=
    (absr;; p) ---> (v <- spec; r;; pure v).

  Theorem refine_unfolded_iff T
          (p: relation CState CState T)
          (spec: relation AState AState T) :
    (forall s__a, absr s__a Err -> False) ->
    (forall s s__a, absr s__a (Val s tt) ->
             (forall s' v, p s (Val s' v) ->
                     (exists s__a', spec s__a (Val s__a' v) /\
                                   absr s__a' (Val s' tt)) \/ spec s__a Err) /\
             (p s Err -> spec s__a Err)) <->
    refines p spec.
  Proof.
    unfold refines, rimpl, and_then, pure; split.
    - propositional. destruct_return. propositional.
      * destruct o1. eapply H0 in H1 as (?&?); eauto.
        edestruct H1 as [(?&?&?)|]; eauto.
        right. intuition eauto 10.
      * intuition; [ exfalso; eauto |].
        propositional.
        destruct o1. eapply H0 in H1 as (?&?); eauto.
    - intros. split.
      * intros. edestruct (H0 s__a (Val s' v)) as [[|]|]; eauto 20.
        ** propositional. intuition.
           *** exfalso; eauto.
           *** propositional. congruence.
        ** propositional. inversion H5. subst. left. eexists; split; eauto.
           destruct o0. eauto.
      * intros. edestruct (H0 s__a Err) as [[|]|]; eauto 20.
        ** propositional. intuition.
           *** exfalso; eauto.
           *** propositional. congruence.
        ** intuition. propositional. intuition.
           *** exfalso; eauto.
           *** propositional. congruence.
  Qed.

  Theorem refine_unfolded T
          (p: relation CState CState T)
          (spec: relation AState AState T) :
    (forall s__a, absr s__a Err -> False) ->
    (forall s s__a, absr s__a (Val s tt) ->
             (forall s' v, p s (Val s' v) ->
                     (exists s__a', spec s__a (Val s__a' v) /\
                                   absr s__a' (Val s' tt)) \/ spec s__a Err) /\
             (p s Err -> spec s__a Err)) ->
    refines p spec.
  Proof. intros. eapply refine_unfolded_iff; eauto. Qed.

  Theorem refine_if_unfolded_iff T (r: relation AState CState unit)
          (p: relation CState CState T)
          (spec: relation AState AState T) :
    (forall s__a, absr s__a Err -> False) ->
    (forall s__a, r s__a Err -> False) ->
    (forall s s__a, absr s__a (Val s tt) ->
             (forall s' v, p s (Val s' v) ->
                     (exists s__a', spec s__a (Val s__a' v) /\
                                   r s__a' (Val s' tt)) \/ spec s__a Err) /\
             (p s Err -> spec s__a Err)) <->
    refines_if r p spec.
  Proof.
    unfold refines_if, rimpl, and_then, pure. intros ? Herr; split.
    - propositional. destruct_return. propositional.
      * destruct o1. eapply H0 in H1 as (?&?); eauto.
        edestruct H1 as [(?&?&?)|]; eauto.
        right. intuition eauto 10.
      * intuition; [ exfalso; eauto |].
        propositional.
        destruct o1. eapply H0 in H1 as (?&?); eauto.
    - intros. split.
      * intros. edestruct (H0 s__a (Val s' v)) as [[|]|]; eauto 20.
        ** propositional. intuition.
           *** exfalso; eauto.
           *** propositional. congruence.
        ** propositional. inversion H5. subst. left. eexists; split; eauto.
           destruct o0. eauto.
      * intros. edestruct (H0 s__a Err) as [[|]|]; eauto 20.
        ** propositional. intuition.
           *** exfalso; eauto.
           *** propositional. congruence.
        ** intuition. propositional. intuition.
           *** exfalso; eauto.
           *** propositional. congruence.
  Qed.

  Section Dynamics.
    Context C_Op (c_sem: Dynamics C_Op CState).
    Notation c_proc := (proc C_Op).
    Notation c_rec_seq := (rec_seq C_Op).
    Notation c_exec := c_sem.(exec).
    Notation c_rexec := c_sem.(rexec).
    Notation c_exec_halt := c_sem.(exec_halt).
    Notation c_rexec_partial := c_sem.(rexec_partial).

    Definition crash_refines T
               (p: c_proc T) (rec: c_rec_seq)
               (exec_spec: relation AState AState _)
               (rexec_spec: relation AState AState _) :=
      refines (c_exec p) exec_spec /\
      refines (c_rexec p rec) rexec_spec.

    Definition halt_refines T r
               (p: c_proc T) (rec: c_rec_seq)
               (exec_partial_spec: relation AState AState _)
               (rexec_partial_spec: relation AState AState _) :=
      refines_if r (c_exec_halt p) exec_partial_spec /\
      refines_if r (c_rexec_partial p rec) rexec_partial_spec.
  End Dynamics.

End Abstraction.

Theorem refines_transitive_abs State1 State2 State3 abs1 abs2 T
        (spec1: relation State1 State1 T)
        (spec2: relation State2 State2 T)
        (spec3: relation State3 State3 T) :
  refines abs1 spec1 spec2 ->
  refines abs2 spec2 spec3 ->
  refines (abs2;; abs1) spec1 spec3.
Proof.
  unfold refines; norm; intros.
  setoid_rewrite H; norm.
  rewrite <- bind_assoc at 1.
  rewrite H0; norm.
Qed.

Theorem refines_trans_bind State1 State2 abs T1 T2
        (r1: relation State1 State1 T1)
        (r2: T1 -> relation State1 State1 T2)
        (r1': relation State2 State2 T1)
        (r2': T1 -> relation State2 State2 T2) :
  refines abs r1 r1' ->
  (forall v, refines abs (r2 v) (r2' v)) ->
  refines abs (and_then r1 r2) (and_then r1' r2').
Proof.
  unfold refines; intros.
  rewrite <- bind_assoc.
  setoid_rewrite H; norm.
  setoid_rewrite H0; norm.
Qed.

Theorem refines_trans_unit State1 State2 abs T2
        (r1: relation State1 State1 unit)
        (r2: unit -> relation State1 State1 T2)
        (r1': relation State2 State2 unit)
        (r2': unit -> relation State2 State2 T2) :
  refines abs r1 r1' ->
  (refines abs (r2 tt) (r2' tt)) ->
  refines abs (and_then r1 r2) (and_then r1' r2').
Proof.
  intros.
  apply refines_trans_bind; auto.
  destruct v; auto.
Qed.

Theorem refines_trans State1 State2 abs T
        (r1 r2: relation State1 State1 T)
        (r1' r2': relation State2 State2 T) :
  refines abs r1 r1' ->
  refines abs r2 r2' ->
  refines abs (r1;; r2) (r1';; r2').
Proof.
  auto using refines_trans_bind.
Qed.

Theorem refines_star State1 State2 (abs: relation State2 State1 unit) T
        (r1: relation State1 State1 T)
        (r2: relation State2 State2 T) :
  (forall a, abs a Err -> False) ->
  refines abs r1 r2 ->
  refines abs (seq_star r1) (seq_star r2).
Proof.
  unfold refines. intros ? Hr.
  rew simulation_seq_value_no_err; auto.
Qed.

Theorem refines_or State1 State2 abs T
        (r1 r1': relation State1 State1 T)
        (r2 r2': relation State2 State2 T) :
  refines abs r1 r2 ->
  refines abs r1' r2' ->
  refines abs (r1 + r1') (r2 + r2').
Proof.
  unfold refines. intros Hr Hr'.
  repeat rew bind_dist_r.
  repeat rew bind_dist_l.
  rew Hr. rew Hr'.
Qed.