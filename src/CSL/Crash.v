Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Abstraction.
Require Import Spec.Layer.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
Require Import CSL.WeakestPre.

From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import base tactics classes.
Set Default Proof Using "Type".
Unset Implicit Arguments.
Import uPred.

Section crash.

Context {OpT: Type -> Type}.
Context `{Λ: Layer OpT} `{irisG OpT Λ Σ}.

(** crashed(P) should hold if P must hold after a crash step.

   The intuition is that if we are given ownership of all resources needed to
   prove the new state interpretation and the crash interpretation, then we
   should be able to derive the state interpretation and P. This should work for
   something like the encoding of state used in the 'heap_lang' Iris example.

   As part of an adequacy proof, we will just have to show that for all such σ1 σ2,
   there exists a Q as below.

   TODO: maybe the thing to the left of the implication should be under a □ modality.
   it would simplify the meta-theory and will probably work
 *)

Definition crashed (P: iProp Σ) : iProp Σ :=
  (∀ σ1 σ2 Q,
      (Q ∗ state_interp σ1 ∗ ⌜crash_step Λ.(sem) σ1 σ2 tt⌝ ==∗ state_interp σ2 ∗ crash_interp σ1 σ2)
    → (Q ∗ state_interp σ1 ∗ ⌜crash_step Λ.(sem) σ1 σ2 tt⌝ ==∗ state_interp σ2 ∗ P))%I.


(* Alternative possible definition, but it seems too awkward to work with *)

(*
Definition crashed (E: coPset) (P: iProp Σ) : iProp Σ :=
  (∀ σ1 σ2 Q, (Q ∗ state_interp σ1 ∗ ⌜crash_step Λ.(sem) σ1 σ2 tt⌝ ={E,∅,∅}▷=∗ state_interp σ2)
    → (Q ∗ state_interp σ1 ∗ ⌜crash_step Λ.(sem) σ1 σ2 tt⌝ ={E,∅,∅}▷=∗ P ∗ state_interp σ2))%I.
*)


Global Instance crashed_ne n :
  Proper (dist n ==> dist n) (crashed).
Proof. rewrite /crashed => P Q Hequiv. repeat f_equiv; eauto. Qed.

Global Instance crashed_proper:
  Proper ((≡) ==> (≡)) (crashed).
Proof. intros ?? Hequiv. apply equiv_dist=>n; apply crashed_ne; auto. Qed. 

Lemma crashed_mono P Q :
  (P -∗ Q) →
  crashed P -∗ crashed Q.
Proof.
  iIntros (HPQ).
  iIntros "Hc". iIntros (σ1 σ2 Q').
  iSpecialize ("Hc" $! σ1 σ2 Q').
  iRevert "Hc".
  iApply impl_mono; auto. by rewrite HPQ.
Qed.

(* TODO: this should be upstreamed. *)
Lemma and_curry: ∀ (PROP : bi) (P Q R : PROP), (P → Q → R)%I ≡ (P ∧ Q → R)%I.
Proof.
  intros.
  apply (anti_symm (⊢)).
  - apply impl_intro_r.
    rewrite and_assoc. by do 2 rewrite impl_elim_l.
  - do 2 apply impl_intro_r. rewrite -and_assoc. apply impl_elim_l.
Qed.

Lemma crashed_plainly P Q:
  crashed P ∗ ■ Q -∗ crashed (P ∗ ■ Q).
Proof.
  iIntros "(Hc&#HQ)".
  iIntros (σ1 σ2 Q').
  iSpecialize ("Hc" $! σ1 σ2 Q').
  iRevert "Hc".
  (* TODO: write a tactic to automatically introduce an implication when the
  spatial context contains 1 assertion *)
  rewrite -impl_wand_1 and_curry impl_elim_l.
  iIntros "H1 H2".
  iFrame "HQ". iMod ("H1" with "H2").
  iModIntro; auto.
Qed.

Lemma crash_interp_crashed P:
  (∀ σ1 σ2, crash_interp σ1 σ2 ==∗ P) →
  crashed P.
Proof.
  intros Hci. iIntros (σ1 σ2 Q) "H1 H2".
  iMod ("H1" with "H2") as "(?&?)". iMod (Hci with "[$]"). iModIntro; iFrame.
Qed.

End crash.