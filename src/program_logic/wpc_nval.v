From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export crash_weakestpre staged_invariant_alt.
Set Default Proof Using "Type".
Import uPred.

Section modality.
Context `{IRISG: !irisGS Λ Σ}.

Definition wpc_nval E (P : iProp Σ) : iProp Σ :=
  (∀ E' e s k Φ Φc,
    ⌜ to_val e = None ⌝ →
    ⌜ E ⊆ E' ⌝ →
    (WPC e @ s; k; E' {{ λ v, P -∗ Φ v }} {{ Φc }}) -∗
    WPC e @ s; k; E' {{ λ v, Φ v }} {{ Φc }}).


Lemma wpc_nval_strong_mono E P P' :
  wpc_nval E P -∗
  ▷ (P -∗ |NC={E}=> P') -∗
  wpc_nval E P'.
Proof.
  iIntros "Hwpc_nval Hwand".
  rewrite /wpc_nval. iIntros (?????? Hnval Hsub) "H".
  iApply wpc_ncfupd.
  iApply "Hwpc_nval"; auto.
  iApply (wpc_step_strong_mono with "[$]"); eauto.
  iSplit; last eauto.
  iNext. iIntros (?) "HP'". iModIntro. iIntros "HP".
  iApply (ncfupd_mask_mono E); auto.
  iMod ("Hwand" with "[$]"). iDestruct ("HP'" with "[$]") as "$".
  eauto.
Qed.

Lemma wpc_nval_True E : ⊢ wpc_nval E True%I.
Proof.
  rewrite /wpc_nval. iIntros (??????) "Hnval Hsub H".
  iApply (wpc_strong_mono with "H"); eauto.
  iSplit; last eauto.
  iIntros (?) "H". iApply "H". eauto.
Qed.

Lemma wpc_nval_intro E P :
  ▷ P -∗ wpc_nval E P.
Proof.
  iIntros "HP".
  iPoseProof (wpc_nval_True) as "Htrue".
  iApply (wpc_nval_strong_mono with "Htrue"); eauto.
Qed.

Lemma wpc_nval_ncfupd E P :
  wpc_nval E (|NC={E}=> P) -∗ wpc_nval E P.
Proof.
  iIntros "HP".
  iApply (wpc_nval_strong_mono with "HP"); eauto.
Qed.

Lemma ncfupd_wpc_nval E P :
  (|NC={E}=> wpc_nval E P) -∗ wpc_nval E P.
Proof.
  iIntros "HP".
  rewrite /wpc_nval. iIntros (?????? Hnval Hsub) "H".
  rewrite ?wpc_unfold. iIntros (mj).
  rewrite /wpc_pre.
  rewrite Hnval.
  iSplit; last first.
  { iDestruct ("H" $! _) as "(_&H)". eauto. }
  iIntros. rewrite ncfupd_eq.
  iSpecialize ("HP" with "[$]").
  iMod (fupd_mask_mono with "HP") as "(HP&HNC)"; auto.
  iSpecialize ("HP" $! E' e s k Φ Φc with "[//] [//]").
  rewrite ?wpc_unfold.
  rewrite /wpc_pre.
  rewrite Hnval.
  iSpecialize ("HP" with "H").
  iDestruct ("HP" $! mj) as "(H&_)".
  iApply ("H" with "[$] [$] [$]").
Qed.

Lemma wpc_nval_elim E1 E2 P e s k Φ Φc :
  to_val e = None →
  E1 ⊆ E2 →
  wpc_nval E1 P -∗
  (WPC e @ s; k; E2 {{ λ v, P -∗ Φ v }} {{ Φc }}) -∗
  WPC e @ s; k; E2 {{ λ v, Φ v }} {{ Φc }}.
Proof.
  iIntros (Hnval Hsub) "Hwpc_nval Hwpc".
  iApply "Hwpc_nval"; eauto.
Qed.

Lemma wpc_nval_elim_wp E1 E2 P e s Φ :
  to_val e = None →
  E1 ⊆ E2 →
  wpc_nval E1 P -∗
  (WP e @ s; E2 {{ λ v, P -∗ Φ v }}) -∗
  WP e @ s; E2 {{ λ v, Φ v }}.
Proof.
  iIntros (Hnval Hsub) "Hwpc_nval Hwpc".
  rewrite wp_eq /wp_def.
  iApply (wpc_nval_elim with "[$]"); eauto.
Qed.

End modality.
