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

  Fixpoint wp T (p: proc T) (post: T -> State -> Prop) : State -> Prop :=
    fun s =>
      match p with
      | Ret v => post v s
      | Prim op => forall v s', step op s s' v ->
                          post v s'
      | Bind p rx =>
        wp p (fun v s' => wp (rx v) post s') s
      end.

  Ltac cleanup :=
    simpl in *;
    unfold pure, and_then, test, rel_or in *;
    propositional.

  Theorem wp_ok T (p: proc T) (post: T -> State -> Prop) :
    forall s, wp p post s ->
         forall s' v, exec p s s' v ->
                 post v s'.
  Proof.
    induction p; cleanup; eauto.
    eapply IHp in H1; eauto; cleanup.
    eapply H in H1; eauto.
  Qed.

  Theorem wp_kat T (p: proc T) (post: T -> State -> Prop) :
    test (wp p post);; exec p --->
         test (wp p post);; v <- exec p; test (post v);; pure v.
  Proof.
    cleanup.
    unfold rimpl; propositional.
    descend; intuition eauto.
    descend; intuition eauto.
    descend; intuition eauto.
    eapply wp_ok; eauto.
  Qed.

  Fixpoint wp_crash T (p: proc T) (crash: State -> Prop) : State -> Prop :=
    fun s =>
      match p with
      | Ret v => crash s
      | Prim op => crash s /\
                  forall v s', step op s s' v ->
                          crash s'
      | Bind p rx =>
        (* crashing at s is handled by wp_crash p (inductively; the other two
 rules includes this *)
        wp_crash p crash s /\
        wp p (fun v s' => wp_crash (rx v) crash s') s
      end.

  Theorem wp_crash_ok T (p: proc T) (crash: State -> Prop) :
    forall s, wp_crash p crash s ->
         forall s' v, exec_crash p s s' v ->
                 crash s'.
  Proof.
    induction p; cleanup; eauto.
    - repeat match goal with
             | [ H: _ \/ _ |- _ ] => destruct H; propositional; eauto
             end.
    - repeat match goal with
             | [ H: _ \/ _ |- _ ] => destruct H; propositional; eauto
             end.
      + eapply IHp; eauto.
        apply exec_crash_noop; cleanup; eauto.
      + eapply wp_ok in H2; eauto.
  Qed.

  Theorem wp_crash_kat T (p: proc T) (crash: State -> Prop) :
    test (wp_crash p crash);; exec_crash p --->
         test (wp_crash p crash);; exec_crash p;; test crash.
  Proof.
    cleanup.
    unfold rimpl; propositional.
    descend; intuition eauto.
    descend; intuition eauto.
    eapply wp_crash_ok; eauto.
  Qed.

End Dynamics.
