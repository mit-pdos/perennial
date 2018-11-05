Require Import Examples.StatDb.Impl.

Require Import Helpers.RelationRewriting.

Require Import Spec.Hoare.
Require Import Spec.HoareTactics.
Require Import Spec.AbstractionSpec.

Definition absr : relation DB.l.(State) Var.l.(State) unit :=
  fun l s _ =>
    fst s = fold_right plus 0 l /\
    snd s = length l.

Definition init_cspec : Specification InitStatus unit Var.State :=
  fun state =>
    {|
      pre := state = (0, 0);
      post := fun state' _ => state' = (0, 0);
      alternate := fun state' (_:unit) => True
    |}.

Definition add_cspec n : Specification unit unit Var.State :=
  fun state =>
    {|
      pre := True;
      post := fun state' (_:unit) => fst state' = (n + fst state) /\
                                     snd state' =  S (snd state);
      alternate := fun state' (_:unit) => True
    |}.

Definition add_rspec n : Specification unit unit Var.State :=
  fun state =>
    {|
      pre := True;
      post := fun state' (_:unit) => fst state' = (n + fst state) /\
                                     snd state' =  S (snd state);
      alternate := fun state' (_:unit) => state' = (0, 0)
    |}.

Definition avg_cspec : Specification nat unit Var.State :=
  fun state =>
    {|
      pre := True;
      post := fun state' v => state = state' /\ v = (fst state / snd state');
      alternate := fun state' v => True
    |}.

Definition avg_rspec : Specification nat unit Var.State :=
  fun state =>
    {|
      pre := True;
      post := fun state' v => state = state' /\ v = (fst state / snd state');
      alternate := fun state' v => state' = (0, 0)
    |}.

Definition recover_spec : Specification unit unit Var.State :=
  fun state =>
    {|
      pre := state = (0, 0);
      post := fun state' (_:unit) => state' = (0, 0);
      alternate := fun state' (_:unit) => state' = (0, 0);
    |}.

Lemma read_op_ok :
  forall i,
    proc_cspec Var.dynamics (read i) (op_spec Var.dynamics (Var.Read i)).
Proof. intros. eapply op_spec_sound. Qed.

Lemma write_op_ok :
  forall i v,
    proc_cspec Var.dynamics (write i v) (op_spec Var.dynamics (Var.Write i v)).
Proof. intros. eapply op_spec_sound. Qed.

Hint Resolve read_op_ok write_op_ok.

Ltac simplify :=
  repeat match goal with
         | |- forall _, _ => intros
         | _ => deex
         | _ => destruct_tuple
         | _ => destruct_tuple
         | [ H: reads _ _ _ _ |- _] => unfold reads in H
         | [ H: puts _ _ _ _ |- _] => unfold puts in H
         | [ u: unit |- _ ] => destruct u
         | |- _ /\ _ => split; [ solve [auto] | ]
         | |- _ /\ _ => split; [ | solve [auto] ]
         | _ => progress simpl in *
         | _ => progress safe_intuition
         | _ => progress subst
         | _ => progress autorewrite with upd in *
         end.

Ltac step :=
  unshelve (step_proc); simplify; finish.

Lemma recover_cok : proc_cspec Var.dynamics (impl.(recover)) recover_spec.
Proof. simpl. eapply ret_cspec; firstorder. Qed.

Lemma recover_idempotent :
  idempotent_crash_step Var.dynamics (fun (t: unit) => recover_spec).
Proof.
  unfold idempotent_crash_step; intuition; exists tt; simpl in *.
  unfold puts in *; firstorder; congruence.
Qed.

Hint Resolve recover_cok recover_idempotent.

Lemma recover_rok : proc_rspec Var.dynamics (impl.(recover)) (impl.(recover)) recover_spec.
Proof. eapply proc_cspec_to_rspec; eauto. intros []; eauto. Qed.

Lemma init_cok :
  proc_cspec Var.dynamics (impl.(init)) (init_cspec).
Proof. eapply ret_cspec; firstorder. Qed.

Lemma add_cok n :
  proc_cspec Var.dynamics (impl.(compile_op) (DB.Add n)) (add_cspec n).
Proof. repeat step. Qed.

Lemma avg_cok :
  proc_cspec Var.dynamics (impl.(compile_op) (DB.Avg)) (avg_cspec).
Proof. repeat step. Qed.

Lemma add_ok n :
  proc_rspec Var.dynamics (impl.(compile_op) (DB.Add n)) impl.(recover) (add_rspec n).
Proof. eapply proc_cspec_to_rspec; [ eapply add_cok |..]; eauto. intros []; eauto. Qed.

Lemma avg_ok :
  proc_rspec Var.dynamics (impl.(compile_op) (DB.Avg)) impl.(recover) (avg_rspec).
Proof. eapply proc_cspec_to_rspec; [ eapply avg_cok |..]; eauto. intros []; eauto. Qed.

Hint Resolve add_ok avg_ok init_cok.

Definition rf : LayerRefinement Var.l DB.l.
Proof.
  refine {| Layer.impl := impl;
            Layer.absr := absr; |}.
  - red; intros.
    destruct op.
    + eapply proc_rspec_crash_refines_op; eauto; unfold spec_impl, absr in *; simplify.
      eapply proc_rspec_impl; [| eapply add_ok].
      unfold spec_impl; simplify; firstorder.
      ** exists (n :: sA). unfold puts; firstorder; simpl; congruence.
      ** exists nil. subst. simplify; firstorder.
    + eapply proc_rspec_crash_refines_op; eauto; unfold spec_impl, absr in *; simplify.
      eapply proc_rspec_impl; [| eapply avg_ok].
      unfold spec_impl; simplify; firstorder.
      ** exists sA. unfold puts; firstorder; simpl; congruence.
      ** exists nil. subst. simplify; firstorder.
  - eapply proc_rspec_recovery_refines_crash_step; [ intros; eapply recover_rok |..]; simplify.
    intuition; exists nil; unfold absr in *; simplify; intuition; subst; simplify; try congruence.
  - eapply proc_cspec_init_ok; [ eapply init_cok |..]; firstorder.
    simpl in H. unfold absr. exists nil. simpl; subst; firstorder.
Qed.
