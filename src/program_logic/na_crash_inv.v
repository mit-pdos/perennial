From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl numbers.
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

Definition na_crash_inv_def N k Q P :=
  (∃ Γ Qr bset, staged_inv Γ N k (⊤ ∖ ↑N) (⊤ ∖ ↑N) ∗ staged_bundle Γ Q Qr false bset ∗
                staged_crash Γ P bset)%I.
Definition na_crash_inv_aux : seal (@na_crash_inv_def). by eexists. Qed.
Definition na_crash_inv := (na_crash_inv_aux).(unseal).
Definition na_crash_inv_eq := (na_crash_inv_aux).(seal_eq).

Ltac crash_unseal :=
  rewrite /na_crash_inv;
  rewrite ?na_crash_inv_eq;
  rewrite /na_crash_inv_def.

Lemma na_crash_inv_alloc N k E P Q:
  ↑N ⊆ E →
  ▷ Q -∗ ▷ □ (Q -∗ P) ={E}=∗ na_crash_inv N (LVL k) Q P ∗ |C={⊤, ∅}_(LVL (S k))=> P.
Proof.
  crash_unseal.
  iIntros (?) "HQ #HQP".
  iMod (staged_inv_init) as (Γ) "#H".
  iMod (staged_inv_alloc Γ N (LVL k) E (⊤ ∖ ↑N) P Q True%I with "[HQ]") as (i') "(Hbundle&#Hval&Hpend)".
  { auto. }
  { iFrame "#". iFrame. iAlways; iIntros; eauto. iSplitL; last done.
    iApply "HQP"; eauto. }
  iModIntro.
  iSplitL "Hbundle".
  { iExists _, _, _. iFrame. iFrame "#". }
  iApply (staged_inv_init_cfupd with "[$]"); eauto.
Qed.

Lemma na_crash_inv_weaken N k Q Q' P :
  □(Q -∗ Q') -∗
  na_crash_inv N k Q P -∗
  na_crash_inv N k Q' P.
Proof.
  crash_unseal.
  iIntros "#HQ' H".
  iDestruct "H" as (? Qr ?) "(Hinv&Hbundle&?)".
  iExists _, Qr, _. iFrame.
  iApply (staged_bundle_weaken_1 with "HQ' Hbundle").
Qed.

Lemma wpc_na_crash_inv_open_modify Qnew s k k' E1 E2 e Φ Φc Q P N :
  ↑N ⊆ E1 →
  S k < k' →
  to_val e = None →
  na_crash_inv N (LVL k') Q P -∗
  (Φc ∧ (Q -∗ WPC e @ NotStuck; (LVL k); (E1 ∖ ↑N); ∅
                    {{λ v, ▷ Qnew v ∗ ▷ □ (Qnew v -∗ P)  ∗ (na_crash_inv N (LVL k') (Qnew v) P -∗ (Φc ∧ Φ v))}}
                    {{ Φc ∗ ▷ P }})) -∗
  WPC e @ s; LVL (S k); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  crash_unseal.
  iIntros (???) "Hbundle Hwp".
  iDestruct "Hbundle" as (???) "(#Hinv&Hbundle&#Hval)".
  iApply (wpc_staged_inv_open _ _ _ _ _ _ _ _ _ _ _ _ Qnew); eauto.
  iFrame "Hinv". iFrame "Hval". iFrame "Hbundle".
  iSplit.
  { iDestruct "Hwp" as "($&_)". }
  iDestruct "Hwp" as "(_&Hwp)".
  iIntros "HQ". iSpecialize ("Hwp" with "HQ").
  iApply (wpc_strong_mono' with "Hwp"); eauto.
  iSplit.
  - iIntros (?) "(HQ&#Hwand'&HQrest)".
    iModIntro. iFrame "HQ Hwand'". iIntros "Hval'".
    iApply "HQrest". iFrame. iExists _, _, _. iFrame "∗ #".
  - iIntros. rewrite difference_diag_L. iModIntro; eauto.
Qed.

Lemma wpc_na_crash_inv_open s k k' E1 E2 e Φ Φc Q P N:
  ↑N ⊆ E1 →
  S k < k' →
  to_val e = None →
  na_crash_inv N (LVL k') Q P -∗
  (Φc ∧ (Q -∗ WPC e @ NotStuck; (LVL k); (E1 ∖ ↑N); ∅
                    {{λ v, ▷ Q ∗ ▷ □ (Q -∗ P) ∗ (na_crash_inv N (LVL k') Q P -∗ (Φc ∧ Φ v))}}
                    {{ Φc ∗ ▷ P }})) -∗
  WPC e @ s; LVL (S k); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (???) "H1 Hwp". iApply (wpc_na_crash_inv_open_modify with "[$] [$]"); auto.
Qed.

Lemma na_crash_inv_open_modify N k' k E E' P Q R:
  ↑N ⊆ E →
  na_crash_inv N k' Q P -∗
  ((Q ∗ (∀ Q', ▷ Q' ∗ □ (Q' -∗ P) ={E∖↑N,E}=∗ na_crash_inv N k' Q' P)) ∨ (C ∗ |={E∖↑N, E}=> na_crash_inv N k' Q P)
   -∗ |={E ∖ ↑N, E'}_k=> R) -∗
  (|={E,E'}_(S (S k))=> R).
Proof.
  crash_unseal.
  iIntros (?) "Hbundle Hwp".
  iDestruct "Hbundle" as (???) "(#Hinv&Hbundle&#Hval)".
  iMod (staged_inv_open with "[$]") as "HQ"; auto.
  iMod (fupd_intro_mask' _ ∅) as "Hclo"; first set_solver.
  iModIntro.
  rewrite Nat_iter_S.
  iModIntro. iNext. iModIntro.
  rewrite Nat_iter_S.
  iModIntro. iNext. iMod "Hclo" as "_".
  iApply ("Hwp" with "[HQ]").
  iDestruct "HQ" as "[(HQ&Hclo)|(?&HC&Hclo)]".
  - iLeft. iFrame. iIntros (Q') "(HQ'&#Hwand')". iMod ("Hclo" $! Q' True%I false with "[HQ']") as "H".
    { iFrame. iAlways. iIntros. iSplitL; last done. by iApply "Hwand'". }
    iModIntro. iExists _, _, _. iFrame "# ∗".
  - iRight. iFrame. iMod "Hclo". iModIntro. iExists _, _, _. iFrame "# ∗".
Qed.

Lemma na_crash_inv_open N k' k E E' P Q R:
  ↑N ⊆ E →
  na_crash_inv N k' Q P -∗
  ((Q ∗ (▷ Q ∗ □ (Q -∗ P) ={E∖↑N,E}=∗ na_crash_inv N k' Q P)) ∨ (C ∗ |={E∖↑N, E}=> na_crash_inv N k' Q P)
   -∗ |={E ∖ ↑N, E'}_k=> R) -∗
  (|={E,E'}_(S (S k))=> R).
Proof.
  iIntros (?) "H1 H2".
  iApply (na_crash_inv_open_modify with "[$]"); auto.
  iIntros "H". iApply ("H2" with "[H]").
  iDestruct "H" as "[H1|H2]".
   - iLeft. iDestruct "H1" as "($&H)". iIntros "HQ". by iMod ("H" $! Q with "[$]").
   - iRight. iFrame.
Qed.

End ci.
