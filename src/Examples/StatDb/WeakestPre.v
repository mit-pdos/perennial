From iris.algebra Require Import auth gmap.
Require Export CSL.WeakestPre.
Require Import CSL.Lifting.
Require Import StatDb.Impl.
Require Import Helpers.RelationTheorems.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".


Class varG Σ := VarG {
                     var_invG : invG Σ;
                     var_alg_inG :> inG Σ (authR (optionUR (exclR natC)));
                     var_reg_gnames: Var.id -> gname
                   }.

Definition reg_map `{varG Σ} (i: Var.id) (v: nat) :=
  own (var_reg_gnames i) (◯ (Excl' v)).
Definition reg_map_auth `{varG Σ} (i: Var.id) (v: nat) :=
  own (var_reg_gnames i) (● (Excl' v)).

Local Notation "i ↦ v" := (reg_map i v) (at level 20) : bi_scope.
Local Notation "i ↦● v" := (reg_map_auth i v) (at level 20) : bi_scope.


Import Var.

Instance varG_irisG `{varG Σ} : irisG Var.Op Var.l Σ :=
  {
    iris_invG := var_invG;
    state_interp := (λ '(ns, nc, nl), Var.Sum ↦● ns ∗ Var.Count ↦● nc ∗ Var.Lock ↦● nl)%I
  }.


Section lifting.
Context `{varG Σ}.

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

Global Instance reg_map_timless i v: Timeless (i ↦ v).
Proof. apply _. Qed.

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

(* Essentially the same as the verification of the spinlock in Iris heap_lang
   except we don't allocate locks or pass the pointer to them; there is a dedicated
   lock register. *)

Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitC) }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitC)].
Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section lock.
  Context `{!varG Σ, !lockG Σ}.

  Definition lock_inv (γ : gname) (P : iProp Σ) : iProp Σ :=
    ((Lock ↦ 0 ∗ P ∗ own γ (Excl ())) ∨ (Lock ↦ 1))%I.

  Definition is_lock (N: namespace) (γ: gname) (P: iProp Σ) : iProp Σ :=
    (inv N (lock_inv γ P))%I.

  Definition locked (γ: gname) : iProp Σ :=
    own γ (Excl ()).

  Global Instance is_lock_persistent N γ R : Persistent (is_lock N γ R).
  Proof. apply _. Qed.

  Global Instance locked_timless γ : Timeless (locked γ).
  Proof. apply _. Qed.

  Lemma lock_init N (R: iProp Σ) E : Lock ↦ 0 -∗ R ={E}=∗ ∃ γ, is_lock N γ R.
  Proof.
    iIntros "Hl HR".
    iMod (own_alloc (Excl ())) as (γ) "Hexcl"; first done.
    iMod (inv_alloc N _ (lock_inv γ R) with "[-]").
    { iNext. iLeft; iFrame. }
    iModIntro; iExists _; done.
  Qed.

  Lemma wp_lock N γ (R: iProp Σ):
    {{{ is_lock N γ R }}} lock {{{ RET tt; locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "#Hlock HΦ". iLöb as "IH".
    wp_loop; wp_bind.
    iInv N as "[HL|>HUL]".
    - iDestruct "HL" as "(>H&?&>?)".
      iApply (wp_cas_suc with "[$]"). iIntros "!> Hl !>"; iFrame.
      rewrite //=. wp_ret. wp_ret.
      iApply "HΦ"; iFrame.
    - iApply (wp_cas_fail with "[$]"); first done. iIntros "!> Hl !>"; iFrame.
      rewrite //=. wp_ret. iApply "IH"; eauto.
  Qed.

  Lemma wp_unlock N γ (R: iProp Σ):
    {{{ is_lock N γ R ∗ locked γ ∗ R }}} unlock {{{ RET tt; True }}}.
  Proof.
    iIntros (Φ) "(#Hlock&Hlocked&HR) HΦ".
    iInv N as "[HL|>HUL]".
    - iDestruct "HL" as "(>H&?&>Htok)".
      iDestruct (own_valid_2 with "Htok Hlocked") as %H => //=.
    - iApply (wp_write with "[$]"); iIntros "!> H !>".
      iSplitR "HΦ"; last by iApply "HΦ".
      iLeft. iFrame.
  Qed.
End lock.