Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Helpers.RelationAlgebra.
Require Import Tactical.ProofAutomation.

Import RelationNotations.

Section Dynamics.
  Context `(sem: Dynamics Op State).
  Notation proc := (proc Op).
  Notation step := sem.(step).
  Notation exec := sem.(exec).
  Notation exec_crash := sem.(exec_crash).

  Definition precondition T := forall (post: T -> State -> Prop), State -> Prop.

  Record WPSetup :=
    { op_wp: forall T, Op T -> precondition T;
      op_wp_ok :
        forall T (op:Op T) post s, op_wp op post s ->
                              forall s' v, step op s s' v ->
                                      post v s'; }.

  Ltac cleanup :=
    simpl in *;
    unfold pure, and_then, test, rel_or in *;
    propositional.

  Context (wp: WPSetup).

  Fixpoint precond T (p: proc T)
    : precondition T :=
    fun post =>
      match p with
      | Ret v => post v
      | Call op => wp.(op_wp) op post
      | Bind p rx =>
        precond p (fun v s' => precond (rx v) post s')
      end.

  Theorem wp_ok :
    forall T (p: proc T) (post: T -> State -> Prop),
    forall s, precond p post s ->
         forall s' v, exec p s s' v ->
                 post v s'.
  Proof.
    intros Hop_wp.
    induction p; cleanup; eauto.
    - eapply wp.(op_wp_ok) in H; eauto.
    - eapply IHp in H1; eauto; cleanup.
      eapply H in H1; eauto.
  Qed.

  Definition crashpre := forall (crash: State -> Prop), State -> Prop.

  Fixpoint crashcond T (p: proc T) : crashpre :=
    fun crash s =>
      match p with
      | Ret v => crash s
      | Call op => crash s /\
                  wp.(op_wp) op (fun v s => crash s) s
      | Bind p rx =>
        (* crashing at s is handled by wp_crash p (inductively; the other two
 rules includes this *)
        crashcond p crash s /\
        precond p (fun v s' => crashcond (rx v) crash s') s
      end.

  Theorem wp_crash_ok T (p: proc T) (crash: State -> Prop) :
    forall s, crashcond p crash s ->
         forall s' v, exec_crash p s s' v ->
                 crash s'.
  Proof.
    induction p; cleanup; eauto.
    - repeat match goal with
             | [ H: _ \/ _ |- _ ] => destruct H; propositional; eauto
             end.
      eapply wp.(op_wp_ok) in H1; eauto; cleanup.
    - repeat match goal with
             | [ H: _ \/ _ |- _ ] => destruct H; propositional; eauto
             end.
      + eapply IHp; eauto.
        apply exec_crash_noop; cleanup; eauto.
      + eapply wp_ok in H2; eauto.
  Qed.

End Dynamics.

Arguments precondition State T : clear implicits.
Arguments crashpre State : clear implicits.
