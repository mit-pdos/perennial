From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl.
From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import staged_invariant crash_weakestpre.
Set Default Proof Using "Type".
Import uPred.

Section ci.
Context `{!irisG Λ Σ}.
Context `{!stagedG Σ}.
Context `{inG Σ (exclR unitO)}.

Definition Tok (γ: gname) :=
  own γ (Excl ()).

Lemma Tok_Tok γ: Tok γ ∗ Tok γ -∗ False.
Proof. iIntros "(H1&H2)". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

Instance timeless_Tok γ: Timeless (Tok γ).
Proof. rewrite /Tok. apply _. Qed.

Definition ci_staged k E1 E2 P : iProp Σ :=
  (|={E1, ∅}=> |={∅, ∅}▷=>^k |={∅, E2}=> P)%I.

Lemma wpc_staged_invariant_aux s k E1 E2 E1' E2' e Φ Φc P Q1 R1 Q2 R2 N γ' :
  ↑N ⊆ E1 →
  (E2' ⊆ E1') →
  (E1 ⊆ E1') →
  (E2' ⊆ E2) →
  □ (Q1 -∗ R1) ∗
  □ (Q2 -∗ R2) ∗
  staged_inv N γ' (ci_staged (2 * (S (S (S k)))) E1' E2' P) ∗
  staged_value N γ' (|={E1 ∖ ↑N, ∅}=> |={∅, ∅}▷=>^(S k)
                     |={∅, E1 ∖ ↑N}=>
                     Q1 ∗ WPC e @ k; E1 ∖ ↑N;E2 {{ v, (Φ v ∧ |={E1,E2}=> Φc) ∗ P }}{{Φc ∗ P}} ∗ Q2) ⊢
  |={E1, ∅}=> |={∅, ∅}▷=>^(S (S (S k))) |={∅, E1}=> R1 ∗ WPC e @ s; S (S k); E1; E2 {{ v, Φ v }} {{Φc}} ∗ R2.
Proof.
  iIntros (????) "(#HQR1&#HQR2&#Hsi&Hwp)".
  iLöb as "IH" forall (Q1 Q2 R1 R2 e) "HQR1 HQR2".
  destruct (to_val e) as [v|] eqn:Hval.
  {
    rewrite Nat_iter_S.
    iMod (staged_inv_open with "[$]") as "(H&Hclo')".
    { set_solver. }
    iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
    iModIntro. rewrite Nat_iter_S. iModIntro. iNext. iModIntro.
    rewrite Nat_iter_S.
    iModIntro. iNext.
    iMod "Hclo" as "_".
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hclo"; first by set_solver+.
    iMod "H". iModIntro.
    rewrite Nat_iter_S. iMod "H".  iModIntro. iNext. iMod "H". iModIntro.
    iApply (step_fupdN_wand with "H").
    iIntros "H".
    iMod "H".
    rewrite wpc_unfold /wpc_pre.
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(HQ1&(H&_)&HQ2)".
    iMod "H" as "(HΦ&HP)".
    iMod "Hclo".
    iMod ("Hclo'" with "[HP]").
    { iSplitL. iApply "HP". iAlways.
      iIntros. rewrite /ci_staged.
      iApply step_fupdN_inner_later; first auto.
      iNext. eauto.
    }
    iModIntro.
    iSplitL "HQ1".
    { by iApply "HQR1". }
    iSplitR "HQ2"; last first.
    { by iApply "HQR2". }
    iSplit.
    - iDestruct "HΦ" as "($&_)". eauto.
    - iDestruct "HΦ" as "(_&HΦ)".
      iMod "HΦ". iMod (fupd_intro_mask' _ ∅) as "?"; first by set_solver.
      iModIntro.
      iApply step_fupdN_later; first by set_solver.
      repeat iNext. by iFrame.
  }
  rewrite (Nat_iter_S ((S (S k)))).
  iMod (staged_inv_open with "[$]") as "(H&Hclo')".
  { set_solver. }
  iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
  rewrite (Nat_iter_S (S k)).
  iModIntro. iModIntro. iNext. iModIntro.
  iModIntro. iNext.
  iMod "Hclo" as "_".
  iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hclo"; first by set_solver+.
  iMod "H". iModIntro.
  iApply (step_fupdN_wand with "H").
  iIntros "H".
  iMod "H".
  iMod "Hclo" as "_".
  iDestruct "H" as "(HQ1&H&HQ2)".
  iSpecialize ("Hclo'" $! _ with "[H]").
  { iSplitL "H". iApply "H".
    iAlways.
    iIntros "H".
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(_&HP)".
    rewrite /ci_staged.
    iMod (fupd_intro_mask') as "Hclo"; [| iMod "HP"].
    { set_solver. }
    iModIntro.
    iApply (step_fupdN_le (S k)).
    { reflexivity. }
    { lia. }
    iApply (step_fupdN_wand with "HP").
    iIntros "HP". iMod "HP". iDestruct "HP" as "((_&HP)&Hclo')".
    iMod "Hclo'".
    iApply fupd_mask_weaken; auto.
  }
  iMod "Hclo'".
  iModIntro.
  iSplitL "HQ1".
  { iApply "HQR1". eauto. }
  iSplitR "HQ2"; last first.
  { iApply "HQR2". eauto. }
  iEval (rewrite wpc_unfold /wpc_pre). rewrite Hval.
  iSplit.
  - iIntros.
    iMod (staged_inv_open with "[$]") as "(H&Hclo')".
    { set_solver. }
    iMod (fupd_intro_mask' _ ∅) as "Hclo''".
    { set_solver. }
    iModIntro. rewrite Nat_iter_S. rewrite Nat_iter_S.
    iModIntro. iNext. iModIntro. iModIntro. iNext.
    iMod "Hclo''" as "_".
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(H&_)".
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hclo''".
    { set_solver. }
    iMod ("H" with "[$]") as "H".
    iModIntro.
    iApply (step_fupdN_wand with "H").
    iIntros "H".
    iSplit; last first.
    { iDestruct "H" as "(_&H)".
      iMod "H" as "(($&?)&$)". eauto.
    }
    iDestruct "H" as "(H&_)".
    iMod "H". iModIntro.
    iDestruct "H" as "(%&H)".
    iSplitL "".
    { destruct s; eauto. }
    iIntros.
    iMod ("H" with "[//]") as "H".
    iModIntro. iNext. iMod "H" as "H".

    iMod "Hclo''" as "_".
    iSpecialize ("Hclo'" $! _ with "[H]").
    { iSplitL "H". iApply "H".
      iAlways. iIntros "H".
      rewrite /ci_staged.
      replace (2 * S (S (S k))) with (S (S (S k)) + S (S (S k))) by lia.
      iApply step_fupdN_inner_plus.
      iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hclo''".
      { set_solver. }
      iMod "H".
      iModIntro.
      iApply (step_fupdN_le (S k)); first reflexivity.
      { lia. }
      iApply (step_fupdN_wand with "H"). iIntros "H".
      iMod "H". iMod "Hclo''" as "_".
      iDestruct "H" as "(_&H&_)".
      iPoseProof (wpc_crash with "H") as "H".
      iModIntro.
      iMod (fupd_intro_mask') as "Hclo"; [| iMod "H"].
      { set_solver. }
      iModIntro.
      iApply (step_fupdN_le (S k)).
      { reflexivity. }
      { lia. }
      iApply (step_fupdN_wand with "H").
      iIntros "HP". iMod "HP". iDestruct "HP" as "((_&HP)&Hclo')".
      iMod "Hclo'".
      iApply fupd_mask_weaken; auto.
    }
    iMod "Hclo'". iModIntro.
    iApply ("IH" with "Hclo' [] []").
    { iAlways. iIntros "H". eauto. }
    { iAlways. iIntros "H". iApply (big_sepL_mono with "H").
      iIntros. iApply (wpc_strong_mono with "[$]"); eauto.
    }
  - iIntros.
    iMod (staged_inv_open with "[$]") as "(H&Hclo')".
    { set_solver. }
    iMod (fupd_intro_mask' _ ∅) as "Hclo''".
    { set_solver. }
    iModIntro. rewrite Nat_iter_S. rewrite Nat_iter_S.
    iModIntro. iNext. iModIntro. iModIntro. iNext.
    iMod "Hclo''" as "_".
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(_&H)".
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hclo''".
    { set_solver. }
    iMod ("H") as "H".
    iModIntro.
    iApply (step_fupdN_wand with "H").
    iIntros "H".
    iMod "H" as "(($&HP)&$)".
    eauto.
Qed.

Lemma wpc_staged_invariant s k E1 E2 E1' E2' e Φ Φc Q P N γ :
  ↑N ⊆ E1 →
  (E2' ⊆ E1') →
  (E1 ⊆ E1') →
  (E2' ⊆ E2) →
  to_val e = None →
  staged_inv N γ (ci_staged (2 * (S (S (S k)))) E1' E2' P) ∗
  staged_value N γ Q ∗
  (▷ (Q) -∗ WPC e @ NotStuck; k; (E1 ∖ ↑N); E2
                {{ λ v, (Φ v ∧ |={E1,E2}=> Φc) ∗ P}} {{ Φc ∗ P }}) ⊢
  WPC e @ s; (S (S k)); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (???? Hval) "(#Hinv&Hval&Hwp)".
  rewrite !wpc_unfold /wpc_pre.
  iSplit; last first.
  {
    iMod (staged_inv_open with "[$]") as "(H&Hclo)"; first auto.
    iMod (fupd_intro_mask' _ ∅) as "Hclo'"; first set_solver+.
    iModIntro.
    iEval (rewrite Nat_iter_S). iModIntro. iNext.
    iDestruct ("Hwp" with "[$]") as "(_&H)".
    iMod "Hclo'".
    iApply (step_fupdN_le (S k)); first by set_solver+.
    { lia. }
    iApply (step_fupdN_wand with "H").
    iIntros "H". iMod "H" as "(($&?)&$)".
    eauto.
  }
  rewrite Hval.
  iIntros (????) "Hstate".
  iMod (staged_inv_open with "[$]") as "(H&Hclo)"; first auto.
  iMod (fupd_intro_mask' _ ∅) as "Hclo'"; first set_solver+.
  iModIntro.
  iEval (rewrite Nat_iter_S). iModIntro. iNext.
  iDestruct ("Hwp" with "[$]") as "(Hwp&_)".
  iMod "Hclo'".
  iMod ("Hwp" with "[$]") as "Hwp". iModIntro.
  iEval (rewrite Nat_iter_S_r).
  iApply (step_fupdN_wand with "Hwp").
  iIntros "Hwp".
  iModIntro. iNext. iModIntro.
  iSplit.
  *
  iDestruct "Hwp" as "(H&_)".
  iMod "H". iModIntro.
  iDestruct "H" as "(%&H)".
  iSplitL "".
  { destruct s; eauto. }
  iIntros.
  iMod ("H" with "[//]") as "H".
  iModIntro. iNext. iMod "H" as "H".
  iSpecialize ("Hclo" $! _ with "[H]").
  { iSplitL "H". iApply "H".
    iAlways.
    iIntros "H".

    replace (2 * S (S (S k))) with (S (S (S k)) + S (S (S k))) by lia.
    iApply step_fupdN_inner_plus.
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hclo''".
    { set_solver. }
    iMod "H".
    iModIntro.
    iApply (step_fupdN_le (S k)); first reflexivity.
    { lia. }
    iApply (step_fupdN_wand with "H"). iIntros "H".
    iMod "H". iMod "Hclo''" as "_".
    iDestruct "H" as "(_&H&_)".
    iPoseProof (wpc_crash with "H") as "H".
    iModIntro.
    iMod (fupd_intro_mask') as "Hclo"; [| iMod "H"].
    { set_solver. }
    iModIntro.
    iApply (step_fupdN_le (S k)).
    { reflexivity. }
    { lia. }
    iApply (step_fupdN_wand with "H").
    iIntros "HP". iMod "HP". iDestruct "HP" as "((_&HP)&Hclo')".
    iMod "Hclo'".
    iApply fupd_mask_weaken; auto.
  }
  iMod "Hclo".
  iModIntro.
  iApply (wpc_staged_invariant_aux s k E1 E2 E1' E2'
                _ Φ Φc P
                (state_interp σ2 a1 (strings.length efs + a2)) _
                ([∗ list] ef ∈ efs, WPC ef @ k; ⊤;∅ {{ v, fork_post v }}{{True}})%I  _ N γ with "[Hclo]"); try assumption.
  { iIntros. iFrame "Hinv". iFrame "Hclo".
    iSplit.
    - eauto.
    - iAlways. iIntros "H". iApply (big_sepL_mono with "H").
      iIntros. iApply (wpc_strong_mono with "[$]"); eauto.
  }
  * iDestruct "Hwp" as "(_&H)".
    iMod "H" as "(($&_)&$)". eauto.
Qed.


End ci.
