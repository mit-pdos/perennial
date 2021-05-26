From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export crash_weakestpre staged_invariant_alt wpc_nval.
Set Default Proof Using "Type".
Import uPred.

Section modality.
Context `{IRISG: !irisGS Λ Σ}.

Definition wp_nval `{!irisGS Λ Σ, !crashG Σ} E1 P :=
  ((∀ mj q g1 ns D κs,
       let E2 :=  ⊤ ∖ D in
       let E2 :=  ⊤ ∖ D in
       global_state_interp g1 ns mj D κs -∗ NC q -∗
     ||={E1|E2,∅|∅}=> ||▷=>^(S (num_laters_per_step ns)) ||={∅|∅,E1|E2}=> global_state_interp g1 ns mj D κs ∗ P ∗ NC q))%I.

Lemma wp_nval_strong_mono E P P' :
  wp_nval E P -∗
  (P -∗ |NC={E}=> P') -∗
  wp_nval E P'.
Proof.
  iIntros "Hwp_nval Hwand".
  rewrite /wp_nval. iIntros (??????) "H HNC".
  iSpecialize ("Hwp_nval" with "[$] [$]").
  iApply (step_fupd2N_inner_fupd).
  iApply (step_fupd2N_inner_wand with "Hwp_nval"); auto.
  iIntros "($&HP&HNC)".
  rewrite ncfupd_eq /ncfupd_def. by iMod ("Hwand" with "[$] [$]") as "$".
Qed.

Lemma wp_nval_True E : ⊢ wp_nval E True%I.
Proof.
  rewrite /wp_nval. iIntros (??????) "H HNC".
  iApply step_fupd2N_inner_later; auto. iNext.
  iFrame.
Qed.

Lemma wp_nval_intro E P :
  P -∗ wp_nval E P.
Proof.
  iIntros "HP".
  iPoseProof (wp_nval_True) as "Htrue".
  iApply (wp_nval_strong_mono with "Htrue"); eauto.
Qed.

Lemma wp_nval_ncfupd E P :
  wp_nval E (|NC={E}=> P) -∗ wp_nval E P.
Proof.
  iIntros "HP".
  iApply (wp_nval_strong_mono with "HP"); eauto.
Qed.

Lemma ncfupd_wp_nval E P :
  (|NC={E}=> wp_nval E P) -∗ wp_nval E P.
Proof.
  iIntros "HP".
  rewrite /wp_nval. iIntros (??????) "H HNC".
  iIntros. rewrite ncfupd_eq.
  iSpecialize ("HP" with "[$]").
  iMod (fupd_mask_mono with "HP") as "(HP&HNC)"; auto.
  iApply ("HP" with "[$] [$]").
Qed.


Context `{!later_tokG IRISG}.
Lemma wp_nval_wpc_nval E P :
  later_tok -∗
  ▷ wp_nval E (later_tok -∗ P) -∗
  wpc_nval E P.
Proof.
  rewrite /wp_nval/wpc_nval. iIntros "Htok H" (E' e s k Φ Φc Hnval Hsub) "Hwp".
  rewrite ?wpc_unfold /wpc_pre. iIntros (mj).
  rewrite Hnval. iSplit; last first.
  { iDestruct ("Hwp" $! _) as "(_&$)". }
  iIntros (q σ1 g1 ns D κ κs nt) "Hσ Hg HNC".
  iDestruct ("Hwp" $! mj) as "(Hwp&_)".
  iMod (later_tok_decr with "[$]") as (ns' Hle) "Hg".
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
  iModIntro.
  simpl. iModIntro. iNext. iModIntro.
  iApply (step_fupd2N_le).
  { apply (num_laters_per_step_exp ns'). lia. }
  iApply (step_fupd2N_le ((S (num_laters_per_step ns')) + S (num_laters_per_step ns'))).
  { lia. }
  simpl. rewrite Nat_iter_add.
  iMod "Hclo'" as "_".
  iMod (fupd2_mask_subseteq E (⊤ ∖ D)) as "Hclo'"; try set_solver.
  iMod ("H" with "[$] [$]") as "H".
  iApply (step_fupd2N_wand with "H"). iNext. iIntros "H".
  simpl. iMod "H". iMod "Hclo'".
  iDestruct "H" as "(Hg&HP&HNC)".
  iMod ("Hwp" with "[$] [$] [$]") as "Hwp".
  iApply (step_fupd2N_wand with "Hwp"). iNext. iIntros "($&Hwp)".
  iIntros. iMod ("Hwp" with "[//]") as "($&Hg&Hwp&$)".
  iMod (later_tok_incr with "[$]") as "(Hg&Htok)".
  iMod (global_state_interp_le with "[$]") as "$".
  { specialize (step_count_next_mono ns' ns). lia. }
  iModIntro. iSpecialize ("HP" with "[$]").
  iApply (wpc0_strong_mono with "Hwp"); auto. iSplit; last eauto.
  iIntros (?) "HΦ". iModIntro. by iApply "HΦ".
Qed.

End modality.
