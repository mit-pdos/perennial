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

Lemma reg_agree i v1 v2 : i ↦ v1 -∗ i ↦● v2 -∗ ⌜ v1 = v2 ⌝.
Proof.
  iIntros "Hf Ha".
    by iDestruct (own_valid_2 with "Ha Hf")
      as %[<-%Excl_included%leibniz_equiv _]%auth_valid_discrete_2.
Qed.

Ltac destruct_state σ H :=
  destruct σ as ((?&?)&?);
  iDestruct H as "(?&?&?)".

Lemma wp_write s E i v' v :
  {{{ ▷ i ↦ v' }}} write i v @ s; E {{{ RET tt; i ↦ v }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown". destruct_state σ "Hown".
  iModIntro. iSplit; first by destruct s.
  iIntros (e2 σ2 Hstep) "!>".
  inversion Hstep; subst.
  destruct i; iFrame;
  iMod (reg_update _ v with "Hi [$]") as "(Hi&$)";
  by iApply "HΦ".
Qed.

Lemma wp_read s E i v :
  {{{ ▷ i ↦ v }}} read i @ s; E {{{ RET v; i ↦ v }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown". destruct_state σ "Hown".
  iModIntro. iSplit; first by destruct s.
  iIntros (e2 σ2 Hstep) "!>".
  inversion Hstep; subst.
  destruct i; iDestruct (reg_agree with "Hi [$]") as "%"; subst;
    iFrame; simpl; by iApply "HΦ".
Qed.

Lemma cas_non_stuck i v1 v2 σ:
  ¬ Var.l.(step) (CAS i v1 v2) σ Err.
Proof.
  intros Hstuck. destruct Hstuck as [Hread|(v'&?&Hread&Hrest)].
  - inversion Hread.
  - destruct nat_eq_dec; subst; [apply bind_pure_no_err in Hrest|]; inversion Hrest.
Qed.

Lemma wp_cas_fail s E i v1 v2 v3 :
  v1 ≠ v2 →
  {{{ ▷ i ↦ v1 }}} cas i v2 v3 @ s; E {{{ RET v1; i ↦ v1 }}}.
Proof.
  iIntros (Hneq Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown". destruct_state σ "Hown".
  iModIntro. iSplit.
  { destruct s; auto using cas_non_stuck. }
  iIntros (e2 σ2 Hstep) "!>".
  inversion Hstep as (v'&σ2'&Hread&Hrest); subst.
  inversion Hread; subst.
  destruct i; iDestruct (reg_agree with "Hi [$]") as "%"; subst;
    iFrame; simpl;
  (destruct (nat_eq_dec); [ by (subst; exfalso; eauto)|];
  inversion Hrest; subst;
  iFrame; by iApply "HΦ").
Qed.

Lemma wp_cas_suc s E i v1 v2 :
  {{{ ▷ i ↦ v1 }}} cas i v1 v2 @ s; E {{{ RET v1; i ↦ v2 }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown". destruct_state σ "Hown".
  iModIntro. iSplit.
  { destruct s; auto using cas_non_stuck. }
  iIntros (e2 σ2 Hstep) "!>".
  inversion Hstep as (v'&σ2'&Hread&Hrest); subst.
  inversion Hread; subst.
  destruct i; iDestruct (reg_agree with "Hi [$]") as "%"; subst;
  (destruct (nat_eq_dec); [| simpl in *; congruence]);
  inversion Hrest as ([]&?&Hputs&Hpure); inversion Hputs; inversion Hpure; subst;
     iMod (reg_update _ v2 with "Hi [$]") as "(Hi&$)"; subst;
    iFrame; simpl;
  inversion Hrest; subst;
  iFrame; by iApply "HΦ".
Qed.

End lifting.