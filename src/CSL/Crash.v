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

(* crashed(P) should hold if P holds after a crash step. *)
Definition crashed (E: coPset) (P: iProp Σ) : iProp Σ :=
  (∀ σ1 σ2, state_interp σ1 ∗ ⌜crash_step Λ.(sem) σ1 σ2 tt⌝ ={E,∅,∅}▷=∗ P ∗ state_interp σ2)%I.

Global Instance crashed_ne E n :
  Proper (dist n ==> dist n) (crashed E).
Proof. rewrite /crashed => P Q Hequiv. repeat f_equiv; eauto. Qed.

Global Instance crashed_proper E:
  Proper ((≡) ==> (≡)) (crashed E).
Proof. intros ?? Hequiv. apply equiv_dist=>n; apply crashed_ne; auto. Qed. 

Lemma crashed_mono E P Q :
  crashed E P -∗ (P ==∗ Q) -∗ crashed E Q.
Proof.
  iIntros "Hc HPQ". iIntros (σ1 σ2) "H".
  iMod ("Hc" $! σ1 σ2 with "H") as "Hc".
  iModIntro. iNext. iMod "Hc" as "(?&?)".
  iMod ("HPQ" with "[$]"). iModIntro. iFrame. 
Qed.
      
Lemma fupd_crashed_strong E1 E2 P:
  (|={E2, E1}=> crashed E1 P) -∗ crashed E2 P.
Proof.
  iIntros "Hc". iIntros (σ1 σ2) "H".
  iMod "Hc". by iApply "Hc".
Qed.
  
Lemma crashed_plainly E P Q:
  crashed E P ∗ ■ Q -∗ crashed E (P ∗ ■ Q).
Proof.
  iIntros "(Hc&HQ)".
  iIntros (σ1 σ2) "H".
  iMod ("Hc" $! σ1 σ2 with "H").
  iModIntro. iFrame; auto.
Qed.

Lemma fupd_crashed E P: (|={E}=> crashed E P) -∗ crashed E P.
Proof. iApply fupd_crashed_strong. Qed.

Lemma crashed_fupd E P: crashed E (|={∅}=> P) -∗ crashed E P.
Proof.
  iIntros "Hc". iIntros (σ1 σ2) "H".
  iMod ("Hc" $! σ1 σ2 with "H") as "Hc".
  iModIntro. iNext. by iMod "Hc" as "(>$&$)".
Qed.
End crash.