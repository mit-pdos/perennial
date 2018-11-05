Require Import Examples.StatDb.Impl.

Import RelationNotations.
Require Import Helpers.RelationRewriting.

Require Import Spec.WeakestPreconditions.
Require Import Spec.WpRefine.

Definition absr : relation DB.l.(State) Var.l.(State) unit :=
  fun l s _ =>
    fst s = fold_right plus 0 l /\
    snd s = length l.

Definition wp : WPSetup Var.dynamics.
Proof.
  refine {| op_wp T (op: Var.Op T) :=
              match op with
              | Var.Read i => fun post s => post (Var.get i s) s
              | Var.Write i v => fun post s => post tt (Var.set i v s)
              end |}.
  hnf; intros.
  destruct op; simpl in *; unfold reads, puts in *; propositional.
  destruct v; eauto.
Defined.

Definition rf : LayerRefinement Var.l DB.l.
Proof.
  refine {| Layer.impl := impl;
            Layer.absr := absr; |}.
  - red; intros.
    split.
    + eapply (wp.(wp_refine)); intros.
      destruct s as [sum' count'].
      unfold absr in H; simpl in *; propositional.
      destruct op; simpl.
      * (* read *)
        unfold puts; descend; intuition eauto.
        unfold absr; simpl; intuition eauto.
      * unfold reads; descend; intuition eauto.
        unfold absr; intuition eauto.
    + admit. (* rexec refinement *)
  - red; intros.
    eapply refine_unfolded; unfold absr; propositional.
    destruct s as [sum count]; simpl in *; propositional.
    destruct v.
    admit. (* recovery transfers crash step *)
  - (* initialize abstraction *) simpl.
    Left.
    unfold and_then, test, rimpl, pure, any, absr; simpl; propositional.
    descend; intuition eauto.
    descend; intuition eauto.
    descend; intuition eauto.
    simpl; auto.
    simpl; auto.
Abort.
