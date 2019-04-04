From iris.algebra Require Import auth agree functions csum cmra.
From RecoveryRefinement.CSL Require Import Counting.
From iris.base_logic.lib Require Export own.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
Require Export CSL.Refinement CSL.NamedDestruct ExMach.WeakestPre CSL.ProofModeClasses.

Definition ghost_tagged_type := {X: Type & X}.
Global Instance ghost_tagged_Equiv : @Equiv ghost_tagged_type := (=).
Global Instance ghost_tagged_equiv : @Equivalence ghost_tagged_type (=).
Proof. apply _. Qed.
(*
  split.
  - intros ?. rewrite /ghost_tagged_Equiv. econstructor. trivial. reflexivity. eauto. intros (X&Ix). exists (Logic.eq_refl) => //=.
  - intros (X&Ix) (Y&Iy) (HeqTy&Heq).
    exists (Logic.eq_sym HeqTy); destruct HeqTy => //=.
  - intros (X&Ix) (Y&Iy) (Z&Iz) (HeqTy1&Heq1) (HeqTy2&Heq2).
    destruct HeqTy1, HeqTy2; exists (Logic.eq_refl) => //=.
    etransitivity; eauto.
Qed.
*)

Class ghost_mapG Σ :=
  { ghost_map_inG :> inG Σ (authR (optionUR (prodR countingR (agreeR (discreteC ghost_tagged_type))))) }.

Definition ghost_mapsto `{ghost_mapG Σ} {A: Type} (γ: gname) (n: Z) (v : A) : iProp Σ :=
  (own γ (◯ Some (Count n, to_agree (existT A v : discreteC ghost_tagged_type))))%I.
Definition ghost_mapsto_auth `{ghost_mapG Σ} {A: Type} (γ: gname) (v : A) : iProp Σ :=
  (own γ (● Some (Count 0, to_agree (existT A v : discreteC ghost_tagged_type))))%I.

Local Notation "l ●↦ v" := (ghost_mapsto_auth l v)
  (at level 20, format "l  ●↦  v") : bi_scope.
Local Notation "l ↦{ q } v" := (ghost_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Local Notation "l ↦ v" := (ghost_mapsto l 0 v) (at level 20) : bi_scope.

Local Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Local Notation "l ↦ -" := (l ↦{0} -)%I (at level 20) : bi_scope.

Section ghost_var_helpers.
Context {Σ} `{ghost_mapG Σ}.

Lemma ghost_var_alloc {A} (a: A):
  (|==> ∃ γ, γ ●↦ a ∗ γ ↦ a)%I.
Proof.
  iMod (own_alloc (● (Some (Count 0, to_agree (existT A a : discreteC ghost_tagged_type))) ⋅
                   ◯ (Some (Count 0, to_agree (existT A a : discreteC ghost_tagged_type)))))
    as (γ) "[H1 H2]".
  { apply auth_valid_discrete_2; split; eauto. split; econstructor. }
  iModIntro. iExists γ. iFrame.
Qed.

Require Eqdep.

Lemma ghost_var_agree {A} γ (a1 a2: A) q :
  γ ●↦ a1 -∗ γ ↦{q} a2 -∗ ⌜ a1 = a2 ⌝.
Proof.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hval.
  apply auth_valid_discrete_2 in Hval as (Hincl&?).
  apply option_included in Hincl as [|(p1&p2&Heq1&Heq2&Hcase)]; first by congruence.
  inversion Heq1; subst. inversion Heq2; subst.
  destruct Hcase as [(Heq1'&Heq2')|Hincl].
  - apply to_agree_inj in Heq2'.
    apply Eqdep.EqdepTheory.inj_pair2 in Heq2'. subst. eauto.
  - apply prod_included in Hincl as (?&Heq2'%to_agree_included).
    apply Eqdep.EqdepTheory.inj_pair2 in Heq2'. subst. eauto.
Qed.

Lemma ghost_var_update {A} γ (a1' a1 a2 : A) :
  γ ●↦ a1 -∗ γ ↦ a2 ==∗ γ ●↦ a1' ∗ γ ↦ a1'.
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _
                     (● (Some (Count 0, to_agree (existT A a1' : discreteC ghost_tagged_type))) ⋅
                      ◯ (Some (Count 0, to_agree (existT A a1' : discreteC ghost_tagged_type))))
                        with "Hγ● Hγ◯") as "[$$]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  done.
Qed.

Lemma named_ghost_var_update {A} γ (a1' a1 a2 : A) i1 i2 :
  named i1 (γ ●↦ a1) -∗ named i2 (γ ↦ a2)
        ==∗ named i1 (γ ●↦ a1') ∗ named i2 (γ ↦ a1').
Proof. unbundle_names; apply ghost_var_update. Qed.

End ghost_var_helpers.


From iris.proofmode Require Import coq_tactics intro_patterns spec_patterns.
From iris.proofmode Require Import tactics.
From stdpp Require Import hlist pretty.

(* This tactic searches for own H (● (Excl' x)) and own H (◯ (Excl' y)) in the context and
   uses ghost_var_agree to prove that x = y. *)
Ltac unify_ghost :=
  match goal with
  | [ |- context[ environments.Esnoc _ ?auth_name (?y ●↦ ?x)] ] =>
    match goal with
    | [ |- context[ ghost_mapsto y _ x ] ] => fail 1
    | [ |- context[ environments.Esnoc _ ?frag_name (y ↦{?q} ?z)] ] =>
      let pat := constr:([(SIdent auth_name nil); (SIdent frag_name nil)]) in
      (iDestruct (ghost_var_agree with pat) as %Hp; inversion_clear Hp; subst; [])
    end
  end.

Module test.
Section test.
Context {Σ} `{ghost_mapG Σ}.
Lemma test {A} γ q (v1 v2: A) : γ ●↦ v1 -∗ γ ↦{q} v2 -∗ ⌜ v1 = v2 ⌝.
Proof. iIntros "H1 H2". by unify_ghost. Qed.
End test.
End test.