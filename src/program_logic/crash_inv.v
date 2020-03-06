From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl.
From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import staged_invariant crash_weakestpre staged_wpc.
From Perennial.program_logic Require Export staged_wpc.
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

Definition crash_inv N k E γ P :=
  (∃ γ', staged_inv N k (E ∖ ↑N) (E ∖ ↑N) γ γ' P)%I.

Definition crash_inv_full N k E γ Q P :=
  (∃ γ' Qr, staged_inv N k (E ∖ ↑N) (E ∖ ↑N) γ γ' P ∗ staged_value N γ Q Qr ∗ □ (Q -∗ P))%I.

Definition crash_inv_pending N k E γ P :=
  (∃ γ', staged_inv N k (E ∖ ↑N) (E ∖ ↑N) γ γ' P ∗ staged_pending γ')%I.

Global Instance crash_inv_pers N k E γ P : Persistent (crash_inv N k E γ P).
Proof. apply _. Qed.

Lemma crash_inv_alloc N k E E' P Q:
  ▷ Q ∗ □ (Q -∗ P) ={E}=∗
  ∃ γ, crash_inv_full N k E' γ Q P ∗ crash_inv_pending N k E' γ P.
Proof.
  iIntros "HQP".
  iDestruct "HQP" as "(HQ&#HQP)".
  iMod (staged_inv_alloc N k E (E' ∖ ↑N) P Q True%I with "[HQ]") as (γ γ') "(#Hinv&Hval&Hpend)".
  { iFrame. iAlways. iIntros. iDestruct ("HQP" with "[$]") as "$". }
  iModIntro.
  iExists γ.
  iSplitL "Hval".
  - iExists γ', _. iFrame. iFrame "Hinv". iAlways; eauto.
  - iExists _. iFrame. iFrame "Hinv".
Qed.

Lemma crash_inv_full_weaken N k E γ Q P:
  crash_inv_full N k E γ Q P -∗ crash_inv N k E γ P.
Proof. iIntros "H". iDestruct "H" as (??) "(?&?)"; eauto. iExists _. iFrame. Qed.

Lemma crash_inv_pending_weaken N k E γ P:
  crash_inv_pending N k E γ P -∗ crash_inv N k E γ P.
Proof. iIntros "H". iDestruct "H" as (?) "(?&?)"; eauto. iExists _. iFrame. Qed.

Lemma wpc_crash_inv_open s k k' E1 E1' E2 e Φ Φc Q P N γ :
  E1 ⊆ E1' →
  ↑N ⊆ E1 →
  S k < k' →
  to_val e = None →
  crash_inv_full N (LVL k') E1' γ Q P -∗
  (Φc ∧ (Q -∗ WPC e @ NotStuck; (LVL k); (E1 ∖ ↑N); ∅
                    {{λ v, Q ∗ (crash_inv_full N (LVL k') E1' γ Q P -∗ (Φ v ∧ Φc))}}
                    {{ Φc ∗ P }})) -∗
  WPC e @ s; LVL (S (S k)); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (????) "Hfull Hwp".
  iDestruct "Hfull" as (??) "(#Hinv&Hval&#Hwand)".
  iApply (wpc_staged_inv_open _ _ _ _ _ _ _ _ _ _ _ (λ _, Q)); eauto.
  iFrame "Hinv". iFrame.
  iSplit.
  { iDestruct "Hwp" as "($&_)". }
  iDestruct "Hwp" as "(_&Hwp)".
  iIntros "HQ". iSpecialize ("Hwp" with "HQ").
  iApply (wpc_strong_mono' with "Hwp"); eauto.
  iSplit.
  - iIntros (?) "(HQ&HQrest)".
    iModIntro. iFrame "HQ".
    iFrame "Hwand". iIntros.
    iApply "HQrest". iExists _, _. iFrame. iFrame "Hinv". iFrame "Hwand".
  - iIntros. rewrite difference_diag_L. iModIntro; eauto.
Qed.

Lemma wpc_crash_inv_open_modify Qnew s k k' E1 E1' E2 e Φ Φc Q P N γ :
  E1 ⊆ E1' →
  ↑N ⊆ E1 →
  S k < k' →
  to_val e = None →
  crash_inv_full N (LVL k') E1' γ Q P -∗
  (Φc ∧ (Q -∗ WPC e @ NotStuck; (LVL k); (E1 ∖ ↑N); ∅
                    {{λ v, Qnew v ∗ □ (Qnew v -∗ P)  ∗ (crash_inv_full N (LVL k') E1' γ (Qnew v) P -∗ (Φ v ∧ Φc))}}
                    {{ Φc ∗ P }})) -∗
  WPC e @ s; LVL (S (S k)); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (????) "Hfull Hwp".
  iDestruct "Hfull" as (??) "(#Hinv&Hval&#Hwand)".
  iApply (wpc_staged_inv_open _ _ _ _ _ _ _ _ _ _ _ Qnew); eauto.
  iFrame "Hinv". iFrame.
  iSplit.
  { iDestruct "Hwp" as "($&_)". }
  iDestruct "Hwp" as "(_&Hwp)".
  iIntros "HQ". iSpecialize ("Hwp" with "HQ").
  iApply (wpc_strong_mono' with "Hwp"); eauto.
  iSplit.
  - iIntros (?) "(HQ&#Hwand'&HQrest)".
    iModIntro. iFrame "HQ Hwand'". iIntros "Hval".
    iApply "HQrest". iExists _, _. iFrame. iFrame "Hinv". iFrame "Hwand'".
  - iIntros. rewrite difference_diag_L. iModIntro; eauto.
Qed.

Lemma wpc_crash_inv_init s k k' N E1 E2 e Φ Φc P γ :
  k' < k →
  ↑N ⊆ E1 →
  crash_inv_pending N (LVL k') E1 γ P ∗
  WPC e @ s; LVL k; E1; E2 {{ Φ }} {{ Φc }} ⊢
  WPC e @ s; LVL (S k); E1; E2 {{ Φ }} {{ Φc ∗ P }}.
Proof.
  iIntros (??) "(H&?)".
  iDestruct "H" as (?) "(?&?)".
  iApply wpc_staged_inv_init; last (by iFrame); eauto.
Qed.

Lemma crash_inv_open N k' k E E' E1 γ P Q R:
  ↑N ⊆ E →
  crash_inv_full N k' E1 γ Q P -∗
  ((Q ∗ (▷ Q ={E∖↑N,E}=∗ crash_inv_full N k' E1 γ Q P)) ∨ (C ∗ |={E∖↑N, E}=> emp)
   -∗ |={E ∖ ↑N, E'}_k=> R) -∗
  (|={E,E'}_(S (S k))=> R).
Proof.
  iIntros (?) "H Hwp".
  iDestruct "H" as (??) "(#Hinv&H&#Hwand)".
  iMod (staged_inv_open with "[H]") as "HQ"; try iFrame "H Hinv"; eauto.
  iMod (fupd_intro_mask' _ ∅) as "Hclo"; first set_solver.
  iModIntro.
  rewrite Nat_iter_S.
  iModIntro. iNext. iModIntro.
  rewrite Nat_iter_S.
  iModIntro. iNext. iMod "Hclo" as "_".
  iApply ("Hwp" with "[HQ]").
  iDestruct "HQ" as "[(HQ&Hclo)|(?&HC&?)]".
  - iLeft. iFrame. iIntros "HQ". iMod ("Hclo" $! Q True%I with "[HQ]") as "H".
    { iFrame. iAlways. iIntros. iApply step_fupdN_inner_later; auto. iNext.
      iDestruct ("Hwand" with "[$]") as "$". }
    iModIntro. iExists _, _. iFrame "H Hinv Hwand".
  - iRight. iFrame.
Qed.

Lemma crash_inv_open_modify N k' k E E' E1 γ P Q R:
  ↑N ⊆ E →
  crash_inv_full N k' E1 γ Q P -∗
  ((Q ∗ (∀ Q', ▷ Q' ∗ □ (Q' -∗ P) ={E∖↑N,E}=∗ crash_inv_full N k' E1 γ Q' P)) ∨ (C ∗ |={E∖↑N, E}=> emp)
   -∗ |={E ∖ ↑N, E'}_k=> R) -∗
  (|={E,E'}_(S (S k))=> R).
Proof.
  iIntros (?) "H Hwp".
  iDestruct "H" as (??) "(#Hinv&H&#Hwand)".
  iMod (staged_inv_open with "[H]") as "HQ"; try iFrame "H Hinv"; eauto.
  iMod (fupd_intro_mask' _ ∅) as "Hclo"; first set_solver.
  iModIntro.
  rewrite Nat_iter_S.
  iModIntro. iNext. iModIntro.
  rewrite Nat_iter_S.
  iModIntro. iNext. iMod "Hclo" as "_".
  iApply ("Hwp" with "[HQ]").
  iDestruct "HQ" as "[(HQ&Hclo)|(?&HC&?)]".
  - iLeft. iFrame. iIntros (Q') "(HQ'&#Hwand')". iMod ("Hclo" $! Q' True%I with "[HQ']") as "H".
    { iFrame. iAlways. iIntros. iApply step_fupdN_inner_later; auto. iNext.
      iDestruct ("Hwand'" with "[$]") as "$". }
    iModIntro. iExists _, _. iFrame "H Hinv Hwand'".
  - iRight. iFrame.
Qed.

End ci.
