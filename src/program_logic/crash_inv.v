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

Definition ci_inv_inner k E1 E2 N (P: iProp Σ) γ : iProp Σ :=
  P ∨ (∃ γ', Tok γ ∗ staged_inv N γ' (ci_staged k E1 E2 P))%I.

Lemma wpc_staged_invariant_aux s k E1 E2 E1' E2' e Φ Φc P Q1 R1 Q2 R2 N1 N2 γ γ' :
  ↑N1 ⊆ E1 →
  ↑N2 ⊆ E1 →
  (E2' ⊆ E1') →
  (E1 ⊆ E1') →
  (E2' ⊆ E2) →
  N1 ## N2 →
  inv N1 (ci_inv_inner (2 * S (S (S k))) E1' E2' N2 P γ) ∗
  □ (Q1 -∗ R1) ∗
  □ (Q2 -∗ R2) ∗
  staged_inv N2 γ' (ci_staged (2 * (S (S (S k)))) E1' E2' P) ∗
  staged_value N2 γ' (|={E1 ∖ ↑N1 ∖ ↑N2, ∅}=> |={∅, ∅}▷=>^(S k)
                     |={∅, E1 ∖ ↑N1 ∖ ↑N2}=>
                     Q1 ∗ WPC e @ k; E1 ∖ ↑N1 ∖ ↑N2;E2 {{ v, (Φ v ∧ |={E1,E2}=> Φc) ∗ P }}{{Φc ∗ P}} ∗ Q2) ⊢
  |={E1, ∅}=> |={∅, ∅}▷=>^(S (S (S k))) |={∅, E1}=> R1 ∗ WPC e @ s; S (S k); E1; E2 {{ v, Φ v }} {{Φc}} ∗ R2.
Proof.
  iIntros (????? Hdisj) "(#Hinv&#HQR1&#HQR2&#Hsi&Hwp)".
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
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo"; first by set_solver+.
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
  iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo"; first by set_solver+.
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
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo''".
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
      iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo''".
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
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo''".
    { set_solver. }
    iMod ("H") as "H".
    iModIntro.
    iApply (step_fupdN_wand with "H").
    iIntros "H".
    iMod "H" as "(($&HP)&$)".
    eauto.
Qed.

Lemma detached_ci_tok k E1 E2 N P γ:
  ▷ ci_inv_inner k E1 E2 N P γ -∗
  Tok γ -∗
  ▷ (P ∗ Tok γ).
Proof.
  iIntros "HCI HTok".
  iNext.
  rewrite /ci_inv_inner.
  iDestruct "HCI" as "[$|H]".
  - iFrame.
  - iDestruct "H" as (?) "(H&?)".
    iDestruct (Tok_Tok with "[$]") as "[]".
Qed.

Lemma wpc_staged_invariant s k E1 E2 E1' E2' e Φ Φc P N1 N2 γ :
  ↑N1 ⊆ E1 →
  ↑N2 ⊆ E1 →
  (E2' ⊆ E1') →
  (E1 ⊆ E1') →
  (E2' ⊆ E2) →
  N1 ## N2 →
  inv N1 (ci_inv_inner (2 * S (S (S k))) E1' E2' N2 P γ) ∗
  Tok γ ∗
  (▷ (P) -∗ WPC e @ NotStuck; k; (E1 ∖ ↑N1 ∖ ↑N2); E2
                {{ λ v, (Φ v ∧ |={E1,E2}=> Φc) ∗ P}} {{ Φc ∗ P }}) ⊢
  WPC e @ s; (S (S k)); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (????? Hdisj) "(#Hinv&Htok&Hwp)".
  rewrite !wpc_unfold /wpc_pre.
  iSplit; last first.
  {
    destruct (to_val e).
    - iInv "Hinv" as "H" "Hclo".
      iDestruct (detached_ci_tok with "[$] [$]") as "(H&Htok)".
      iDestruct ("Hwp" with "[$]") as "(_&H)".
      iIntros.
      iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo'".
      { set_solver. }
      iMod "H". iModIntro.
      iApply (step_fupdN_le (S k)); first by set_solver+.
      { lia. }
      iApply (step_fupdN_wand with "H").
      iIntros "H". iMod "H" as "(($&?)&$)".
      eauto.
    - iInv "Hinv" as "H" "Hclo".
      iDestruct (detached_ci_tok with "[$] [$]") as "(H&Htok)".
      iDestruct ("Hwp" with "[$]") as "(_&H)".
      iIntros.
      iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo'".
      { set_solver. }
      iMod "H". iModIntro.
      iApply (step_fupdN_le (S k)); first by set_solver+.
      { lia. }
      iApply (step_fupdN_wand with "H").
      iIntros "H". iMod "H" as "(($&?)&$)".
      eauto.
  }
  destruct (to_val e).
  - iInv "Hinv" as "H" "Hclo".
    iDestruct (detached_ci_tok with "[$] [$]") as "(H&Htok)".
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo'".
    { set_solver+. }
    iDestruct ("Hwp" with "[$]") as "(H&_)".
    iMod "H" as "(($&_)&HP)".
    iMod "Hclo'".
    iMod ("Hclo" with "[-]"); last eauto.
    iLeft. iFrame.
  - iIntros (????) "Hstate".
    iInv "Hinv" as "H" "Hclo".
    iDestruct (detached_ci_tok with "[$] [$]") as "(H&Htok)".
    iDestruct ("Hwp" with "[$]") as "(Hwp&_)".
    replace (↑ N2 : coPset) with (∅ ∪ ↑N2 : coPset) at 1 by set_solver.
    replace (E1 ∖ ↑N1) with (((E1 ∖ ↑N1) ∖ ↑N2) ∪ ↑N2) at 2; last first.
    { assert ((↑N1: coPset) ## (↑N2: coPset)). set_solver.
      clear Hdisj.
      assert (↑N2 ⊆ E1 ∖ ↑N1) by set_solver.
      rewrite difference_union_L. set_solver.
    }
    iSpecialize ("Hwp" with "[$]").
    iMod (fupd_mask_frame_r with "Hwp") as "Hwp".
    { set_solver. }
    rewrite left_id_L.
    iMod (fupd_intro_mask' (↑N2) ∅) as "Hclo'".
    { set_solver. }
    iModIntro. do 2 iEval (rewrite Nat_iter_S_r).
    iApply (step_fupdN_wand with "Hwp").
    iIntros "Hwp".
    iMod (staged_inv_alloc N2 _
             (|={E1', ∅}=> |={∅, ∅}▷=>^(2 * S (S (S k))) |={∅, E2'}=>P)%I _ with "[Hwp]")
      as (γ') "(#Hsi&Hval)".
    { iSplitL "Hwp". iApply "Hwp".
       iAlways. iIntros "(_&Hwp)".
       iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
       iMod "Hwp".
       iModIntro.
       iApply step_fupdN_later; eauto.
       iNext. iDestruct "Hwp" as "((?&HP)&Hclo')".
       iMod "Hclo" as "_". iApply fupd_mask_weaken; eauto.
    }
    iMod "Hclo'" as "_".
    iMod (staged_inv_open with "[$]") as "(H&Hclo')".
    { set_solver. }
    rewrite difference_diag_L.
    iModIntro. iNext. iModIntro. iModIntro. iNext.
    iModIntro.
    iSplit.
    *
    iDestruct "H" as "(H&_)".
    iMod "H". iModIntro.
    iDestruct "H" as "(%&H)".
    iSplitL "".
    { destruct s; eauto. }
    iIntros.
    iMod ("H" with "[//]") as "H".
    iModIntro. iNext. iMod "H" as "H".
    iSpecialize ("Hclo'" $! _ with "[H]").
    { iSplitL "H". iApply "H".
      iAlways.
      iIntros "H".

      replace (2 * S (S (S k))) with (S (S (S k)) + S (S (S k))) by lia.
      iApply step_fupdN_inner_plus.
      iMod (fupd_intro_mask' _ (E1 ∖ ↑N1 ∖ ↑N2)) as "Hclo''".
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
    iAssert (|={E1 ∖ ↑N1 ∖ ↑N2,E1 ∖ ↑N1}=> staged_value N2 γ' _)%I with "[Hclo']" as "H".
    {
    iApply fupd_mask_frame.
    2: { iMod "Hclo'". iModIntro.
         rewrite difference_empty_L.
         iApply (fupd_mask_same).
         rewrite (comm_L (∪)).
      assert (↑N2 ⊆ E1 ∖ ↑N1) by set_solver.
      rewrite difference_union_L. set_solver.
      iModIntro. eauto.
    }
    { set_solver. }
    }
    iMod "H".
    iMod ("Hclo" with "[Htok]") as "_".
    { iNext. iRight. iExists _. iFrame. iFrame "Hsi". }
    iModIntro.
    iApply (wpc_staged_invariant_aux s k E1 E2 E1' E2'
                  _ Φ Φc P
                  (state_interp σ2 a1 (strings.length efs + a2)) _
                  ([∗ list] ef ∈ efs, WPC ef @ k; ⊤;∅ {{ v, fork_post v }}{{True}})%I  _ N1 N2 γ with "[H]"); try assumption.
    { iIntros. iFrame "Hinv". iFrame "H".
      iFrame "Hsi". iSplit.
      - eauto.
      - iAlways. iIntros "H". iApply (big_sepL_mono with "H").
        iIntros. iApply (wpc_strong_mono with "[$]"); eauto.
    }
    * iDestruct "H" as "(_&H)".
      iMod "H" as "(($&_)&$)". eauto.
Qed.


End ci.
