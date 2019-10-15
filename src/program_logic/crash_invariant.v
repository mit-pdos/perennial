From iris.algebra Require Import excl.
From iris.proofmode Require Import base tactics classes.
From Perennial.program_logic Require Export crash_weakestpre.
Set Default Proof Using "Type".

Class crash_invG Σ := CrashInvG { crash_tokG :> inG Σ (exclR unitO) }.
Definition crash_invΣ : gFunctors := #[GFunctor (exclR unitO)].

Instance subG_crash_invΣ : subG crash_invΣ Σ → crash_invG Σ.
Proof. solve_inG. Qed.

Section crash_inv.
Context `{!irisG Λ Σ, crash_invG Σ} (N: namespace).
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Record crash_name := { crash_ename : gname ; crash_dname : gname }.

Definition crash_open Γ := (own (crash_dname Γ)) (Excl ()).
Definition crash_closed Γ := (own (crash_ename Γ)) (Excl ()).

Definition crash_inv_raw (Γ: crash_name) (R: iProp Σ) : iProp Σ :=
  ((crash_open Γ ∗ R) ∨ crash_closed Γ)%I.

Definition crash_inv Γ R := inv N (crash_inv_raw Γ R).

Global Instance crash_inv_persistent Γ R : Persistent (crash_inv Γ R).
Proof. apply _. Qed.
Global Instance crash_open_timeless Γ : Timeless (crash_open Γ).
Proof. apply _. Qed.
Global Instance crash_closed_timeless Γ : Timeless (crash_closed Γ).
Proof. apply _. Qed.

Global Instance crash_inv_ne Γ : NonExpansive (crash_inv Γ).
Proof. rewrite /crash_inv/crash_inv_raw. solve_proper. Qed.

Lemma crash_inv_alloc E R:
  ▷ R ={E}=∗ ∃ Γ, crash_inv Γ R ∗ crash_closed Γ.
Proof.
  iIntros "HR".
  iMod (own_alloc (Excl ())) as (ename) "Hγe"; first done.
  iMod (own_alloc (Excl ())) as (dname) "Hγd"; first done.
  set (Γ := {| crash_ename := ename; crash_dname := dname |}).
  iMod (inv_alloc N E (crash_inv_raw Γ R) with "[Hγd HR]") as "Hinv".
  { iLeft. iNext. iFrame. }
  iModIntro. iExists Γ. by iFrame.
Qed.

Lemma crash_closed_exclusive Γ : crash_closed Γ -∗ crash_closed Γ -∗ False.
Proof. iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %[]. Qed.

Lemma crash_open_exclusive Γ : crash_open Γ -∗ crash_open Γ -∗ False.
Proof. iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %[]. Qed.

Lemma wpc_crash_inv_alloc s E e Φ P:
  ▷ P ∗ (∀ Γ, crash_closed Γ -∗ crash_inv Γ P -∗ WPC e @ s ; E; ↑N {{ Φ }} {{ ▷ crash_closed Γ }}) -∗
    WPC e @ s ; E ; ∅ {{ Φ }} {{ ▷ P }}.
Proof.
  iIntros "(HP&H)".
  (* XXX: fix when accessors typeclasses are setup *)
  iApply fupd_wpc.
  iMod (crash_inv_alloc E P with "HP") as (Γ) "(#Hinv&Hclo)".
  iModIntro.
  iDestruct ("H" with "[$] [$]") as "H".
  iApply (wpc_strong_mono with "H"); auto.
  { set_solver+. }
  iSplit; first auto. iIntros "H".
  iInv "Hinv" as "H'" "Hclo".
  iApply fupd_mask_weaken; first by set_solver+.
  iNext. iDestruct "H'" as "[(?&$)|?]".
  { iExFalso. iApply (crash_closed_exclusive with "[$] [$]"). }
Qed.

Lemma wpc_inv_disj s E1 E2 e Φ P Q :
  ↑N ⊆ E2 →
  (▷ P ∗ ▷ P -∗ False) →
  (▷ Q ∗ ▷ Q -∗ False) →
  inv N (P ∨ Q) ∗ WPC e @ s ; E1; E2 {{ Φ }} {{ ▷ P }} ⊢ WPC e @ s; E1 ; E2 {{ Φ }} {{ ▷ Q }}.
Proof.
  iIntros (HN HPP HQQ) "(#Hinv&H)".
  iApply (wpc_strong_mono with "H"); auto.
  iSplit; first auto.
  iIntros "HP". iInv "Hinv" as "H"; first auto.
  iModIntro.
  iDestruct "H" as "[HP'|HQ]".
  { iExFalso. iApply HPP. iFrame. }
  iSplitL "HP".
  { iNext. auto. }
  { eauto. }
Qed.

Lemma wpc_inv_disj' s E1 E2 e Φ P Q :
  ↑N ⊆ E1 →
  ↑N ⊆ E2 →
  (▷ P ∗ ▷ P ={∅}=∗ False) →
  (▷ Q ∗ ▷ Q ={∅}=∗ False) →
  inv N (P ∨ Q) ∗ (▷ P -∗ WPC e @ s ; E1; E2 {{ Φ }} {{ ▷ P }}) ⊢ (▷ Q -∗ WPC e @ s; E1 ; E2 {{ Φ }} {{ ▷ Q }}).
Proof.
  iIntros (HN1 HN2 HPP HQQ) "(#Hinv&H) HQ".
  iApply (wpc_strong_mono with "[H HQ]").
  { eauto. }
  { reflexivity. }
  { reflexivity. }
  { iApply fupd_wpc. iInv "Hinv" as "HI".
    iDestruct "HI" as "[HP|HQ']"; last first.
    - iApply (fupd_mask_mono ∅).
      { set_solver+. }
      { iMod (HQQ with "[$]"). eauto. }
    - iSplitL "HQ".
      { iModIntro. by iRight. }
        by iApply "H".
  }
  iSplit; first auto.
  iIntros "HP". iInv "Hinv" as "H"; first auto.
  iDestruct "H" as "[HP'|HQ]".
  { iApply (fupd_mask_mono ∅).
    { set_solver+. }
    { iMod (HPP with "[$]"). eauto. }
  }
  iModIntro.
  iSplitL "HP".
  { iNext. auto. }
  { eauto. }
Qed.

Lemma wpc_crash_inv_open s E e Φ Γ P:
  ↑N ⊆ E →
  crash_inv Γ P ∗ ▷ crash_closed Γ ∗ (▷ (crash_open Γ ∗ P)
                                        -∗ WPC e @ s ; E; ↑N {{ Φ }} {{ ▷ (crash_open Γ ∗ P) }}) -∗
    WPC e @ s ; E ; ↑N {{ Φ }} {{ ▷ crash_closed Γ }}.
Proof.
  iIntros (HE) "(#Hinv&Hclo&H)".
  rewrite /crash_inv/crash_inv_raw.
  iApply (wpc_inv_disj' _ _ _ _ _ (crash_open Γ ∗ P) with "[H] [Hclo]").
  { auto. }
  { reflexivity. }
  { iIntros "((>?&?)&(>?&?))".
    iModIntro. iApply (crash_open_exclusive with "[$] [$]"). }
  { iIntros "(>?&>?)".
    iModIntro. iApply (crash_closed_exclusive with "[$] [$]"). }
  { iFrame "Hinv". iIntros.
    by iApply "H".
  }
  by iFrame.
Qed.

Lemma wpc_crash_inv_close s E e Φ Γ P:
  ↑N ⊆ E →
  crash_inv Γ P ∗ ▷ (crash_open Γ ∗ P) ∗ (WPC e @ s ; E; ↑N {{ Φ }} {{ ▷ crash_closed Γ }}) -∗
    WPC e @ s ; E ; ↑N {{ Φ }} {{ ▷ (crash_open Γ ∗ P) }}.
Proof.
  iIntros (HE) "(#Hinv&Hclo&H)".
  rewrite /crash_inv/crash_inv_raw.
  iApply (wpc_inv_disj' _ _ _ _ _ (crash_closed Γ) (crash_open Γ ∗ P)%I with "[H] [Hclo]").
  { auto. }
  { reflexivity. }
  { iIntros "(>?&>?)".
    iModIntro. iApply (crash_closed_exclusive with "[$] [$]"). }
  { iIntros "((>?&?)&(>?&?))".
    iModIntro. iApply (crash_open_exclusive with "[$] [$]"). }
  { iSplitL "Hinv".
    { by rewrite comm. }
    iIntros. by iApply "H".
  }
  by iFrame.
Qed.

End crash_inv.
