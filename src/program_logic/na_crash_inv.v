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

Definition na_crash_inv_def Γ N k :=
  (staged_inv Γ N k (⊤ ∖ ↑N) (⊤ ∖ ↑N))%I.
Definition na_crash_inv_aux : seal (@na_crash_inv_def). by eexists. Qed.
Definition na_crash_inv := (na_crash_inv_aux).(unseal).
Definition na_crash_inv_eq := (na_crash_inv_aux).(seal_eq).

Definition na_crash_bundle_def Γ N k Q bset :=
  (∃ Qr, staged_inv Γ N k (⊤ ∖ ↑N) (⊤ ∖ ↑N) ∗ staged_bundle Γ Q Qr false bset)%I.
Definition na_crash_bundle_aux : seal (@na_crash_bundle_def). by eexists. Qed.
Definition na_crash_bundle := (na_crash_bundle_aux).(unseal).
Definition na_crash_bundle_eq := (na_crash_bundle_aux).(seal_eq).

Definition na_crash_val_def Γ P bset :=
  (staged_crash Γ P bset)%I.
Definition na_crash_val_aux : seal (@na_crash_val_def). by eexists. Qed.
Definition na_crash_val := (na_crash_val_aux).(unseal).
Definition na_crash_val_eq := (na_crash_val_aux).(seal_eq).

Definition na_crash_pending_def Γ N k P :=
  (∃ i, staged_inv Γ N k (⊤ ∖ ↑N) (⊤ ∖ ↑N) ∗ staged_crash_pending Γ P i)%I.
Definition na_crash_pending_aux : seal (@na_crash_pending_def). by eexists. Qed.
Definition na_crash_pending := (na_crash_pending_aux).(unseal).
Definition na_crash_pending_eq := (na_crash_pending_aux).(seal_eq).

Ltac crash_unseal :=
  rewrite /na_crash_inv/na_crash_val/na_crash_pending/na_crash_bundle;
  rewrite ?na_crash_inv_eq ?na_crash_val_eq ?na_crash_pending_eq ?na_crash_bundle_eq;
  rewrite /na_crash_inv_def/na_crash_val_def/na_crash_pending_def/na_crash_bundle_def.

Global Instance na_crash_inv_pers Γ N k : Persistent (na_crash_inv Γ N k).
Proof. crash_unseal. apply _. Qed.

Global Instance na_crash_val_pers Γ P bset : Persistent (na_crash_val Γ P bset).
Proof. crash_unseal. apply _. Qed.


Lemma na_crash_inv_init N k E:
  ⊢ |={E}=> ∃ Γ, na_crash_inv Γ N k.
Proof. crash_unseal. iMod (staged_inv_init) as (Γ) "H". iExists Γ. iFrame "H". eauto. Qed.

Lemma na_crash_inv_alloc Γ N k E P Q:
  ↑N ⊆ E →
  na_crash_inv Γ N k -∗
  ▷ Q -∗ □ (Q -∗ P) ={E}=∗
  ∃ i, na_crash_bundle Γ N k Q {[i]} ∗ na_crash_val Γ P {[i]} ∗ na_crash_pending Γ N k P.
Proof.
  crash_unseal.
  iIntros (?) "#Hinv HQ #HQP".
  iMod (staged_inv_alloc Γ N k E (⊤ ∖ ↑N) P Q True%I with "[HQ]") as (i') "(Hbundle&#Hval&Hpend)".
  { auto. }
  { iFrame "#". iFrame. iAlways; iIntros; eauto. rewrite right_id. iApply "HQP"; eauto. }
  iModIntro. iExists i'. iFrame "#".
  iSplitL "Hbundle".
  - iExists _. iFrame.
  - iExists _. eauto.
Qed.

Lemma na_crash_inv_pending_weaken Γ N k P:
  na_crash_pending Γ N k P -∗ na_crash_inv Γ N k.
Proof. crash_unseal. iIntros "H". iDestruct "H" as (?) "(?&?)"; eauto. Qed.

Lemma na_crash_bundle_weaken Γ N k Q Q' bset :
  □(Q -∗ Q') -∗
  na_crash_bundle Γ N k Q bset -∗
  na_crash_bundle Γ N k Q' bset.
Proof.
  crash_unseal.
  iIntros "#HQ' H".
  iDestruct "H" as (Qr) "[Hinv Hbundle]".
  iExists Qr; iFrame.
  iApply (staged_bundle_weaken_1 with "HQ' Hbundle").
Qed.

Lemma wpc_na_crash_inv_open_modify Γ Qnew s k k' E1 E2 e Φ Φc Q P bset N :
  ↑N ⊆ E1 →
  S k < k' →
  to_val e = None →
  na_crash_bundle Γ N (LVL k') Q bset -∗
  na_crash_val Γ P bset -∗
  (Φc ∧ (Q -∗ WPC e @ NotStuck; (LVL k); (E1 ∖ ↑N); ∅
                    {{λ v, Qnew v ∗ □ (Qnew v -∗ P)  ∗ (na_crash_bundle Γ N (LVL k') (Qnew v) bset -∗ (Φ v ∧ Φc))}}
                    {{ Φc ∗ P }})) -∗
  WPC e @ s; LVL (S (S k)); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  crash_unseal.
  iIntros (???) "Hbundle Hval Hwp".
  iDestruct "Hbundle" as (?) "(#Hinv&Hbundle)".
  iApply (wpc_staged_inv_open _ _ _ _ _ _ _ _ _ _ _ _ Qnew); eauto.
  iFrame "Hinv". iFrame "Hval". iFrame "Hbundle".
  iSplit.
  { iDestruct "Hwp" as "($&_)". }
  iDestruct "Hwp" as "(_&Hwp)".
  iIntros "HQ". iSpecialize ("Hwp" with "HQ").
  iApply (wpc_strong_mono' with "Hwp"); eauto.
  iSplit.
  - iIntros (?) "(HQ&#Hwand'&HQrest)".
    iModIntro. iFrame "HQ Hwand'". iIntros "Hval".
    iApply "HQrest". iFrame. iFrame "Hinv". iExists _. iFrame.
  - iIntros. rewrite difference_diag_L. iModIntro; eauto.
Qed.

Lemma wpc_na_crash_inv_open Γ s k k' E1 E2 e Φ Φc Q P bset N:
  ↑N ⊆ E1 →
  S k < k' →
  to_val e = None →
  na_crash_bundle Γ N (LVL k') Q bset -∗
  na_crash_val Γ P bset -∗
  (Φc ∧ (Q -∗ WPC e @ NotStuck; (LVL k); (E1 ∖ ↑N); ∅
                    {{λ v, Q ∗ □ (Q -∗ P) ∗ (na_crash_bundle Γ N (LVL k') Q bset -∗ (Φ v ∧ Φc))}}
                    {{ Φc ∗ P }})) -∗
  WPC e @ s; LVL (S (S k)); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (???) "H1 H2 Hwp". iApply (wpc_na_crash_inv_open_modify with "[$] [$]"); auto.
Qed.

Lemma wpc_na_crash_inv_init Γ s k k' N E2 e Φ Φc P :
  k' < k →
  na_crash_pending Γ N (LVL k') P ∗
  WPC e @ s; LVL k; ⊤; E2 {{ Φ }} {{ Φc }} ⊢
  WPC e @ s; LVL (S k); ⊤; E2 {{ Φ }} {{ Φc ∗ P }}.
Proof.
  crash_unseal.
  iIntros (?) "(H&?)".
  iDestruct "H" as (?) "(?&?)".
  iApply wpc_staged_inv_init; last (by iFrame); eauto.
Qed.

Lemma wpc_na_crash_inv_init_wand Γ s k k' N E2 e Φ Φc P :
  k' < k →
  na_crash_pending Γ N (LVL k') P -∗
  WPC e @ s; LVL k; ⊤; E2 {{ Φ }} {{ P -∗ Φc }} -∗
  WPC e @ s; LVL (S k); ⊤; E2 {{ Φ }} {{ Φc }}.
Proof.
  crash_unseal.
  iIntros (?) "H ?".
  iDestruct "H" as (?) "(?&?)".
  iApply wpc_staged_inv_init_wand; last (by iFrame); eauto.
Qed.

Lemma wpc_na_crash_inv_big_sepS_init_wand `{Countable A} (σ: gset A)(P: A → iProp Σ) k s E2 e Φ Φc  :
  ([∗ set] a ∈ σ, ∃ Γ N k', ⌜ k' < k ⌝ ∗ na_crash_pending Γ N (LVL k') (P a)) -∗
  WPC e @ s; LVL k; ⊤; E2 {{ Φ }} {{ ([∗ set] a ∈ σ, P a) -∗ Φc }} -∗
  WPC e @ s; LVL (k + size σ); ⊤; E2 {{ Φ }} {{ Φc }}.
Proof.
  iInduction σ as [| x σ ?] "IH" using set_ind_L forall (Φc).
  - rewrite size_empty right_id. iIntros "_ Hwp".
    iApply (wpc_mono with "Hwp"); eauto.
    rewrite big_sepS_empty //=. iIntros "H". by iApply "H".
  - rewrite big_sepS_union; last by set_solver.
    rewrite big_sepS_singleton.
    iIntros "(HPx&Hrest)". iDestruct "HPx" as (?? k' Hlt) "Hpending".
    iIntros "Hwp". replace (k + size ({[x]} ∪ σ)) with (S (k + size σ)); last first.
    { rewrite size_union; last by set_solver. rewrite size_singleton. lia. }
    iApply (wpc_na_crash_inv_init_wand with "Hpending").
    { lia. }
    iApply ("IH" with "Hrest").
    iApply (wpc_mono with "Hwp"); auto.
    iIntros "Hwand Hrest HP". iApply "Hwand".
    rewrite big_sepS_union ?big_sepS_singleton; last by set_solver.
    iFrame.
Qed.

Lemma na_crash_inv_open_modify Γ N k' k E E' P Q R bset:
  ↑N ⊆ E →
  na_crash_bundle Γ N k' Q bset -∗
  na_crash_val Γ P bset -∗
  ((Q ∗ (∀ Q', ▷ Q' ∗ □ (Q' -∗ P) ={E∖↑N,E}=∗ na_crash_bundle Γ N k' Q' bset)) ∨ (C ∗ |={E∖↑N, E}=> na_crash_bundle Γ N k' Q bset)
   -∗ |={E ∖ ↑N, E'}_k=> R) -∗
  (|={E,E'}_(S (S k))=> R).
Proof.
  crash_unseal.
  iIntros (?) "Hbundle Hwp".
  iDestruct "Hbundle" as (?) "(#Hinv&Hbundle)".
  iMod (staged_inv_open with "[$]") as "HQ"; auto.
  iMod (fupd_intro_mask' _ ∅) as "Hclo"; first set_solver.
  iIntros "H".
  iModIntro.
  rewrite Nat_iter_S.
  iModIntro. iNext. iModIntro.
  rewrite Nat_iter_S.
  iModIntro. iNext. iMod "Hclo" as "_".
  iApply ("H" with "[HQ]").
  iDestruct "HQ" as "[(HQ&Hclo)|(?&HC&Hclo)]".
  - iLeft. iFrame. iIntros (Q') "(HQ'&#Hwand')". iMod ("Hclo" $! Q' True%I false with "[HQ']") as "H".
    { iFrame. iAlways. iIntros. rewrite right_id. by iApply "Hwand'". }
    iModIntro. iExists _. iFrame "H Hinv Hwand'".
  - iRight. iFrame. iMod "Hclo". iModIntro. iExists _. iFrame. iFrame "#".
Qed.

Lemma na_crash_inv_open Γ N k' k E E' P Q R bset:
  ↑N ⊆ E →
  na_crash_bundle Γ N k' Q bset -∗
  na_crash_val Γ P bset -∗
  ((Q ∗ (▷ Q ∗ □ (Q -∗ P) ={E∖↑N,E}=∗ na_crash_bundle Γ N k' Q bset)) ∨ (C ∗ |={E∖↑N, E}=> na_crash_bundle Γ N k' Q bset)
   -∗ |={E ∖ ↑N, E'}_k=> R) -∗
  (|={E,E'}_(S (S k))=> R).
Proof.
  iIntros (?) "H1 H2 H3".
  iApply (na_crash_inv_open_modify with "[$] [$]"); auto.
  iIntros "H". iApply ("H3" with "[H]").
  iDestruct "H" as "[H1|H2]".
   - iLeft. iDestruct "H1" as "($&H)". iIntros "HQ". by iMod ("H" $! Q with "[$]").
   - iRight. iFrame.
Qed.

End ci.
