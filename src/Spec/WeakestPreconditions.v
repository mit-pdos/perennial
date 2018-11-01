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

  Context (op_wp: forall T, Op T -> precondition T).

  Definition op_wp_ok :=
    forall T (op:Op T) post s, op_wp op post s ->
                          forall s' v, step op s s' v ->
                                  post v s'.

  Fixpoint wp T (p: proc T)
    : precondition T :=
    fun post =>
      match p with
      | Ret v => post v
      | Prim op => op_wp op post
      | Bind p rx =>
        wp p (fun v s' => wp (rx v) post s')
      end.

  Ltac cleanup :=
    simpl in *;
    unfold pure, and_then, test, rel_or in *;
    propositional.

  Theorem wp_ok :
    op_wp_ok ->
    forall T (p: proc T) (post: T -> State -> Prop),
    forall s, wp p post s ->
         forall s' v, exec p s s' v ->
                 post v s'.
  Proof.
    intros Hop_wp.
    induction p; cleanup; eauto.
    - eapply Hop_wp in H; eauto.
    - eapply IHp in H1; eauto; cleanup.
      eapply H in H1; eauto.
  Qed.

  Theorem wp_op_kat :
    (forall T (op:Op T) post,
        test (op_wp op post);; step op --->
             test (op_wp op post);; v <- step op; test (post v);; pure v) ->
    op_wp_ok.
  Proof.
    unfold op_wp_ok.
    cleanup.
    specialize (H _ op post s s' v); simpl in H.
    match type of H with
    | ?P -> _ =>
      let HP := fresh in
      assert P as HP; [ | specialize (H HP); propositional ]
    end.
    descend; intuition eauto.
  Qed.

  Theorem wp_kat
          T (p: proc T) (post: T -> State -> Prop) :
    (forall T (op:Op T) post,
        test (op_wp op post);; step op --->
             test (op_wp op post);; v <- step op; test (post v);; pure v) ->
    test (wp p post);; exec p --->
         test (wp p post);; v <- exec p; test (post v);; pure v.
  Proof.
    cleanup; unfold rimpl; propositional.
    descend; intuition eauto.
    descend; intuition eauto.
    descend; intuition eauto.
    eapply wp_ok; eauto.
    eapply wp_op_kat; eauto.
  Qed.

  Definition crashpre := forall (crash: State -> Prop), State -> Prop.

  Fixpoint wp_crash T (p: proc T) : crashpre :=
    fun crash s =>
      match p with
      | Ret v => crash s
      | Prim op => crash s /\
                  op_wp op (fun v s => crash s) s
      | Bind p rx =>
        (* crashing at s is handled by wp_crash p (inductively; the other two
 rules includes this *)
        wp_crash p crash s /\
        wp p (fun v s' => wp_crash (rx v) crash s') s
      end.

  Theorem wp_crash_ok T (p: proc T) (crash: State -> Prop) :
    op_wp_ok ->
    forall s, wp_crash p crash s ->
         forall s' v, exec_crash p s s' v ->
                 crash s'.
  Proof.
    intros Hop_ok.
    induction p; cleanup; eauto.
    - repeat match goal with
             | [ H: _ \/ _ |- _ ] => destruct H; propositional; eauto
             end.
      eapply Hop_ok in H1; eauto; cleanup.
    - repeat match goal with
             | [ H: _ \/ _ |- _ ] => destruct H; propositional; eauto
             end.
      + eapply IHp; eauto.
        apply exec_crash_noop; cleanup; eauto.
      + eapply wp_ok in H2; eauto.
  Qed.

  Theorem wp_crash_kat T (p: proc T) (crash: State -> Prop) :
    (forall T (op:Op T) post,
        test (op_wp op post);; step op --->
             test (op_wp op post);; v <- step op; test (post v);; pure v) ->
    test (wp_crash p crash);; exec_crash p --->
         test (wp_crash p crash);; exec_crash p;; test crash.
  Proof.
    cleanup; unfold rimpl; propositional.
    descend; intuition eauto.
    descend; intuition eauto.
    eapply wp_crash_ok; eauto.
    eapply wp_op_kat; eauto.
  Qed.

End Dynamics.

Arguments precondition State T : clear implicits.
Arguments crashpre State : clear implicits.
