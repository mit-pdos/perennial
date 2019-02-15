Require Import Mergesort.
Require Import Orders.
From RecoveryRefinement Require Import Helpers.MachinePrimitives.

Local Coercion is_true : bool >-> Sortclass.
Require Import Arith Omega.

Module PIDOrder <: TotalLeBool.
  Definition t := uint64.
  Definition leb x y :=
    match compare x y with
    | Eq => true
    | Lt => true
    | Gt => false
    end.
  Theorem leb_total : forall x y, leb x y \/ leb y x.
  Proof.
    unfold leb; intros.
    destruct_with_eqn (compare x y); destruct_with_eqn (compare y x); eauto.
    apply Nat.compare_gt_iff in Heqc.
    apply Nat.compare_gt_iff in Heqc0.
    omega.
  Qed.
End PIDOrder.


From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Spec.InjectOp.
From RecoveryRefinement Require Import Helpers.MachinePrimitives.
From RecoveryRefinement Require Import Helpers.RelationAlgebra.

From iris.algebra Require Import auth frac_auth.
From iris.base_logic.lib Require Import invariants.


(**
 * Resource algebra for PIDs.  Each process owns its own PID.
 *)

Module PID.

  Definition pidRAT : Type := list uint64.

  Module S := Sort PIDOrder.

  Instance pidRAop : Op pidRAT :=
    fun x1 x2 =>
      x1 ++ x2.

  Instance pidRAValid : Valid pidRAT :=
    fun x => List.NoDup x.

  Instance pidRACore : PCore pidRAT :=
    fun x => Some nil.

  Instance pidEquiv : Equiv pidRAT :=
    fun x1 x2 =>
      Permutation x1 x2.

  Definition pidRA_mixin : RAMixin pidRAT.
  Proof.
    split; try apply _; try done.
    all: eauto.

    - intros x y He.
      unfold equiv, pidEquiv in He.
      unfold impl, valid, pidRAValid.
      intros; eapply Permutation_NoDup; eauto.

    - unfold op, pidRAop.
      intros x y z.
      admit.

    - intros x cx H.
      unfold pcore, pidRACore in H.
      inversion H; clear H; subst.
      unfold op, pidRAop.
      simpl; eauto.

    - intros x cx H.
      unfold pcore, pidRACore in *.
      inversion H; clear H; subst.
      eauto.

    - intros.
      unfold pcore, pidRACore in *.
      inversion H0; clear H0; subst.
      eexists; split; eauto.
      unfold included.
      exists nil.
      unfold op, pidRAop; simpl.
      eauto.

    - unfold valid, pidRAValid.
      intros.
      unfold op, pidRAop in *.
      admit.
  Admitted.

  Canonical Structure pidRAC := discreteC pidRAT.
  Canonical Structure pidRA := discreteR pidRAT pidRA_mixin.

  Class pidG Σ := PIDG { pid_inG :> inG Σ pidRA }.


  Instance pidRA_cmra_discrete : CmraDiscrete pidRA.
  Proof. apply discrete_cmra_discrete. Qed.

  Instance pidRA_cmra_total : CmraTotal pidRA.
  Proof. intro x. eexists. eauto. Qed.


  (* Helpers to use the resource algebra *)
  Lemma mlistRA_valid_auth_frag l : ✓ (l) ↔ List.NoDup l.
  Proof.
    unfold valid, pidRAValid.
    intuition eauto.
  Qed.

End PID.
