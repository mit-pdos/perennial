From iris.algebra Require Import auth gmap.
Require Export CSL.WeakestPre.
Require Import CSL.Lifting.
Require Import StatDb.Impl.
Require Import Helpers.RelationTheorems.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".


Class statG Σ := StatG {
                     stat_invG : invG Σ;
                     stat_alg_inG :> inG Σ (authR (optionUR (exclR natC)));
                     stat_reg_gnames: Var.id -> gname
                   }.

Definition reg_map `{statG Σ} (i: Var.id) (v: nat) :=
  own (stat_reg_gnames i) (◯ (Excl' v)).
Definition reg_map_auth `{statG Σ} (i: Var.id) (v: nat) :=
  own (stat_reg_gnames i) (● (Excl' v)).
  
Local Notation "i ↦ v" := (reg_map i v) (at level 20) : bi_scope.
Local Notation "i ↦● v" := (reg_map_auth i v) (at level 20) : bi_scope.


Import Var.

Instance statG_irisG `{statG Σ} : irisG Var.Op Var.l Σ :=
  {
    iris_invG := stat_invG;
    state_interp := (λ '(ns, nc, nl), Var.Sum ↦● ns ∗ Var.Count ↦● nc ∗ Var.Lock ↦● nl)%I
  }.
                                     

Section lifting.
Context `{statG Σ}.

Lemma reg_update i vnew v1 v2 : i ↦ v1 -∗ i ↦● v2 ==∗ i ↦ vnew ∗ i ↦● vnew.
Proof.
  iIntros "Hf Ha".
    iMod (own_update_2 _ _ _ (● Excl' vnew ⋅ ◯ Excl' vnew) with "Ha Hf") as "[$$]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    done.
Qed.

Lemma wp_write s E i v' v :
  {{{ ▷ i ↦ v' }}} write i v @ s; E {{{ RET tt; i ↦ v }}}.
Proof.
  iIntros (Φ) ">Hi HΦ".
  iApply wp_lift_atomic_step; first done.
  iIntros (σ) "Hown". destruct σ as ((ns&nc)&nl).
  iDestruct "Hown" as "(Howns&Hownc&Hownl)".
  iModIntro. iSplit.
  {
    destruct s; auto. iPureIntro. rewrite /non_errorable => Hin.
    apply bind_pure_no_err in Hin.
    inversion Hin.
  }
  iIntros (e2 σ2 efs Hstep).
  iNext.
  destruct Hstep as ([]&?&Hstep&Hpure).
  inversion Hstep; subst.
  inversion Hpure; subst.
  destruct i; simpl; iFrame;
  iMod (reg_update _ v with "Hi [$]") as "(Hi&$)";
  iSplitR ""; auto;
  iModIntro; by iApply "HΦ".
Qed.
End lifting.