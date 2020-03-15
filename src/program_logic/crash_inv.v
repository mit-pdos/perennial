From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl.
From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import staged_invariant crash_weakestpre staged_wpc.
Set Default Proof Using "Type".
Import uPred.

Section ci.
Context `{!irisG Λ Σ}.
Context `{!stagedG Σ}.
Context `{!crashG Σ}.
Context `{inG Σ (exclR unitO)}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Definition crash_inv N P :=
  (∃ γ, inv N (P ∨ (C ∗ staged_done γ)))%I.

Definition crash_inv_pending N P :=
  (∃ γ, inv N (P ∨ (C ∗ staged_done γ)) ∗ staged_pending γ)%I.

Global Instance crash_inv_pers N P : Persistent (crash_inv N P).
Proof. apply _. Qed.

Lemma crash_inv_alloc N E P:
  ▷ P ={E}=∗ crash_inv N P ∗ crash_inv_pending N P.
Proof.
  iIntros "HP".
  iMod (pending_alloc) as (γ) "Hpending".
  iMod (inv_alloc N E (P ∨ (C ∗ staged_done γ)) with "[HP]") as "#Hinv".
  { by iLeft. }
  iSplitL ""; iExists γ; eauto.
Qed.

Lemma crash_inv_pending_weaken N P:
  crash_inv_pending N P -∗ crash_inv N P.
Proof. iIntros "H". iDestruct "H" as (?) "(?&?)"; eauto. iExists _. iFrame. Qed.

Lemma wpc_crash_inv_init' s k N E e Φ Φc P :
  crash_inv_pending N P ∗
  WPC e @ s; (k); ⊤; E {{ Φ }} {{ Φc }} ⊢
  WPC e @ s; (S k); ⊤; E {{ Φ }} {{ Φc ∗ P }}.
Proof.
  iIntros "(Hpending&H)".
  iDestruct "Hpending" as (γ) "(#Hinv&Hpending)".
  iApply (wpc_strong_crash_frame with "H"); auto.
  iIntros "HC". replace (S k -k) with (S O) by lia => //=.
  iInv "Hinv" as "H" "Hclo". simpl.
  iMod (fupd_intro_mask' _ ∅) as "Hclo'"; first by set_solver+.
  do 3 iModIntro. iDestruct "H" as "[HP|(_&Hfalse)]".
  - iFrame. iModIntro. iMod "Hclo'".
    iMod (pending_upd_done with "Hpending") as "Hdone".
    iMod ("Hclo" with "[Hdone HC]"); eauto.
  - iDestruct (pending_done with "[$] [$]") as %[].
Qed.

Lemma wpc_crash_inv_init s k N E e Φ Φc P :
  crash_inv_pending N P ∗
  WPC e @ s; LVL (k); ⊤; E {{ Φ }} {{ Φc }} ⊢
  WPC e @ s; LVL (S k); ⊤; E {{ Φ }} {{ Φc ∗ P }}.
Proof.
  iIntros "(HC&HWP)".
  pose proof (SS_LVL k).
  iApply (wpc_idx_mono); first eassumption.
  iApply wpc_crash_inv_init'; iFrame.
  iApply (wpc_idx_mono with "[$]"); eauto.
Qed.

Lemma crash_inv_open N E P:
  ↑N ⊆ E →
  crash_inv N P ={E,E∖↑N}=∗
  (▷ P ∗ (▷ P ={E∖↑N,E}=∗ True)) ∨ (C ∗ |={E∖↑N,E}=> True).
Proof.
  iIntros (?) "H". iDestruct "H" as (γ) "#Hinv".
  iInv "Hinv" as "[HP|>(#HC&Hdone)]" "Hclo".
  - iLeft. iModIntro. iFrame "HP". iIntros "HP".
    by iMod ("Hclo" with "[$]").
  - iRight. iModIntro. iFrame "HC".
    iMod ("Hclo" with "[Hdone]"); eauto.
Qed.

Lemma crash_inv_open_NC N E P:
  ↑N ⊆ E →
  crash_inv N P -∗
  NC ={E,E∖↑N}=∗
  (▷ P ∗ (▷ P ={E∖↑N,E}=∗ True) ∗ NC).
Proof.
  iIntros (?) "H HNC". iMod (crash_inv_open with "[$]") as "[H|(HC&_)]"; auto.
  { iModIntro. by iFrame. }
  iDestruct (NC_C with "[$] [$]") as %[].
Qed.

End ci.
