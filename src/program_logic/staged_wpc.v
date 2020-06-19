From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl numbers.
From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import staged_invariant crash_weakestpre.
Set Default Proof Using "Type".
Import uPred.

Section staged_inv_wpc.
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

Opaque staged_bundle.

Lemma staged_inv_init_cfupd Γ s k k' N E1 e Φ Φc P i:
  k' ≤ k →
  ↑N ⊆ E1 →
  staged_inv Γ N (k') (E1 ∖ ↑N) (E1 ∖ ↑N) ∗
  staged_crash_pending Γ P i -∗
  |C={E1, ∅}_(S (S k))=> P.
Proof.
  iIntros (Hle Hin)  "(#Hinv&Hpending)".
  iIntros "HΦc".
  iApply (step_fupdN_inner_wand _ E1 _ (S (S k')) with "[HΦc Hpending]"); eauto; try lia.
  iPoseProof (staged_inv_weak_open with "[$]") as "H"; eauto.
  iApply (step_fupdN_inner_wand _ E1 with "H"); auto.
  iIntros "HP". iApply step_fupdN_later; auto.
Qed.

Lemma wpc_staged_inv_init' Γ s k k' N E1 E2 e Φ Φc P i:
  k' ≤ k →
  ↑N ⊆ E1 →
  staged_inv Γ N (k') (E1 ∖ ↑N) (E1 ∖ ↑N) ∗
  staged_crash_pending Γ P i ∗
  WPC e @ s; (S (S k)); E1; E2 {{ Φ }} {{ Φc }} ⊢
  WPC e @ s; (2 * (S (S k))); E1; E2 {{ Φ }} {{ Φc ∗ P }}.
Proof.
  iIntros (Hle Hin) "(#Hinv&Hpending&H)".
  iApply (wpc_strong_crash_frame s s _ _ E1 _ _ with "H"); try auto.
  { lia. }
  replace (2 * S (S k) - S (S k)) with (S (S k)) by lia.
  iApply (staged_inv_init_cfupd); eauto.
Qed.

Lemma wpc_staged_inv_open_aux' Γ s k k' k'' E1 E1' E2 e Φ Φc P Q N bset :
  E1 ⊆ E1' →
  ↑N ⊆ E1 →
  k'' ≤ k →
  (2 * (S k'')) ≤ k' →
  (2 * (S k)) ≤ k' →
  staged_inv Γ N k' (E1' ∖ ↑N) (E1' ∖ ↑N) ∗
  NC ∗
  staged_bundle Γ (WPC e @ k''; E1 ∖ ↑N; ∅ {{ v, ▷ Q v ∗ ▷ □ (Q v -∗ P) ∗ (staged_bundle Γ (Q v) True false bset -∗ Φc ∧ Φ v)}}{{Φc ∗ ▷ P}}) Φc true bset ∗
  staged_crash Γ P bset
  ⊢ |={E1,E1}_(S (2 * S (S k)))=>
     WPC e @ s; 2 * S (S k); E1; E2 {{ v, Φ v }} {{Φc}} ∗ NC.
Proof.
  iIntros (?????) "(#Hsi&HNC&Hwp&#Hstaged_crash)".
  iLöb as "IH" forall (e).
  destruct (to_val e) as [v|] eqn:Hval.
  {
    rewrite Nat_iter_S.
    iMod (staged_inv_open with "[$]") as "[(H&Hclo')|Hcrash]"; auto.
    {
      iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
      iModIntro. rewrite Nat_iter_add. iModIntro. iNext. iModIntro.
      rewrite Nat_iter_S.
      iModIntro. iNext.
      iMod "Hclo" as "_".
      rewrite Nat_iter_S.
      iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
      iModIntro. iModIntro. iNext.


      iModIntro.
      iApply step_fupdN_later; first reflexivity. iNext.
      iApply step_fupdN_later; first reflexivity. iNext.
      iMod "Hclo".
      rewrite wpc_unfold /wpc_pre.
      rewrite wpc_unfold /wpc_pre.
      rewrite Hval.
      iDestruct "H" as "(H&_)".
      iMod ("H" with "[$]") as "((HQ&#HQP&HΦ)&HNC)".
      iMod ("Hclo'" $! _ True%I false with "[HQ]").
      { iSplitL. iApply "HQ". iIntros "!>".
        iIntros. iSplitL; last eauto. iApply "HQP"; eauto.
      }
      iModIntro. iSplitR "HNC"; last by iFrame.
      iSplit.
      - iIntros "HNC". iDestruct ("HΦ" with "[$]") as "(_&$)". eauto.
      - iDestruct ("HΦ" with "[$]") as "(HΦ&_)".
        iIntros "HC".
        iApply step_fupdN_inner_later; first by set_solver.
        repeat iNext.
        iApply step_fupdN_inner_later; first by set_solver.
        repeat iNext.
        by iFrame.
    }
    {
      iDestruct "Hcrash" as "(HΦc&HC&Hclo')".
      iDestruct (NC_C with "[$] [$]") as "[]".
    }
  }
  iEval (rewrite (Nat_iter_S _)).
  iMod (staged_inv_open with "[$]") as "[(H&Hclo')|Hcrash]"; auto;
    last first.
  {
      iDestruct "Hcrash" as "(HΦc&HC&Hclo')".
      iDestruct (NC_C with "[$] [$]") as "[]".
  }
  iMod (fupd_intro_mask' _ ∅) as "Hclo"; first by set_solver+.
  rewrite Nat_iter_add.
  rewrite (Nat_iter_S (S k)).
  iModIntro. iModIntro. iNext. iModIntro.
  iModIntro. iNext.
  iMod "Hclo" as "_".
  iSpecialize ("Hclo'" $! _ Φc true with "[H]").
  { iSplitL "H".
    - iNext. iApply "H".
    - iAlways. iIntros "HC H".
    iPoseProof (wpc_crash with "H") as "H".
    iSpecialize ("H" with "[$]").
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hclo".
    { set_solver. }
    iMod "H". iModIntro.
    iApply (step_fupdN_le (2 * S k'')); eauto.
    replace (2 * (((S k'')))) with (S k'' + S k'') by lia.
    rewrite Nat_iter_add.
    iEval rewrite step_fupdN_S_fupd.
    iApply (step_fupdN_wand with "H").
    iIntros "HP".
    iMod "HP". iMod "Hclo".
    iApply (step_fupdN_inner_wand with "HP"); eauto.
    { set_solver+. }
    iIntros "($&$)".
  }
  iMod "Hclo'".
  rewrite -Nat_iter_add. iApply step_fupdN_inner_later; first reflexivity.
  iNext.
  iEval (rewrite wpc_unfold /wpc_pre). rewrite Hval.
  iFrame.
  iSplit.
  - iIntros.
    iMod (staged_inv_open with "[$]") as "[(H&Hclo')|Hcrash]"; auto;
      last first.
    {
      iDestruct "Hcrash" as "(HΦc&HC&Hclo')".
      iDestruct (NC_C with "[$] [$]") as "[]".
    }
    iMod (fupd_intro_mask' _ ∅) as "Hclo''".
    { set_solver. }
    iModIntro. rewrite Nat_iter_S.
    iModIntro. iNext. rewrite Nat_iter_add.
    rewrite Nat_iter_S.
    iModIntro. iModIntro. iNext.
    iMod "Hclo''" as "_".
    rewrite wpc_unfold /wpc_pre.
    rewrite Hval. iDestruct "H" as "(H&_)".
    iMod ("H" with "[$] [$]") as "H".
    iModIntro.
    iApply (step_fupdN_le (S k'')); [ auto | lia |].
    iApply (step_fupdN_wand with "H").
    iIntros "H".
    rewrite right_id Nat_iter_S.
    iMod "H". iModIntro. iNext.
    iDestruct "H" as "(%&H)".
    iApply step_fupdN_inner_later; first reflexivity. do 2 iNext.
    iSplitL "".
    { destruct s; eauto. }
    iIntros.
    iMod ("H" with "[//]") as "H".
  iEval rewrite Nat_iter_S.
  iModIntro. iModIntro. iNext.
  rewrite Nat_iter_add.
  iModIntro. iApply (step_fupdN_le (S k'')); [ auto | lia |].
  iApply (step_fupdN_wand with "H"). iIntros "H".
  rewrite right_id.
  iEval rewrite Nat_iter_S.
  do 2 iMod "H". iModIntro. iNext.
  iMod "H".
  iMod "H".
  iModIntro.
  iApply (step_fupdN_le (S k'')); [ auto | lia |].
  iApply (step_fupdN_wand with "H"). iIntros "H".
  iMod "H".
  iDestruct "H" as "(Hσ&H&Hefs&HNC)".
  iSpecialize ("Hclo'" $! _ Φc true with "[H]").
  { iSplitL "H". iApply "H".
    iAlways.
    iIntros "HC H".
    iPoseProof (wpc_crash with "H") as "H".
    iSpecialize ("H" with "[$]").
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hclo".
    { set_solver. }
    iMod "H". iModIntro.
    iApply (step_fupdN_le (2 * S k)); eauto.
    replace (2 * (((S k)))) with (S k + S k) by lia.
    rewrite Nat_iter_add.
    iEval rewrite step_fupdN_S_fupd.
    iApply (step_fupdN_le (S k'')); [ auto | lia |].
    iApply (step_fupdN_wand with "H").
    iIntros "HP".
    iMod "HP". iMod "Hclo".
    iApply (step_fupdN_inner_wand with "HP"); eauto.
    { set_solver+. }
    { lia. }
    iIntros "($&$)".
  }
  iMod "Hclo'".
  iMod (fupd_intro_mask' _ ∅) as "Hclo''"; first by set_solver+.
  iModIntro. iModIntro. iNext. iMod "Hclo''" as "_".
  iModIntro.
  iApply step_fupdN_inner_frame_l; iFrame.
  iSpecialize ("IH" with "HNC Hclo'").
  iApply (step_fupdN_inner_wand with "IH"); auto.
  iIntros "($&$)".
  iApply (big_sepL_mono with "Hefs").
  iIntros. iApply (wpc_strong_mono' with "[$]"); eauto.
  { lia. }
  { set_solver +. }
  { iSplit; first auto. iIntros. iApply fupd_mask_weaken; eauto; set_solver. }
  - iIntros.
    iMod (staged_inv_open with "[$]") as "[(H&Hclo')|Hcrash]"; auto; last first.
    {
      iDestruct "Hcrash" as "(?&?&Hclo)".
      iMod "Hclo". iIntros. iApply step_fupdN_inner_later; try set_solver+.
      iNext. iNext.
      iApply step_fupdN_inner_later; try set_solver+.
      do 2 iNext; eauto.
    }
    iMod (fupd_intro_mask' _ ∅) as "Hclo''".
    { set_solver. }
    replace (S (2 * (S (S k)))) with (S (S ((S k) + (S (S k))))) by lia.
    iIntros "#HC".
    iModIntro. do 2 rewrite Nat_iter_S.
    iModIntro. iNext. iModIntro. iModIntro. iNext.
    iPoseProof (wpc_crash with "H [$]") as "H".
    iMod "Hclo''" as "_".
    iMod "H". iModIntro.
    rewrite Nat_iter_add.
    iApply (step_fupdN_le (S k'')); [ auto | lia |].
    iApply (step_fupdN_wand with "H"). iIntros "H".
    iEval rewrite Nat_iter_S.
    iMod "H".
    iMod (fupd_intro_mask' _ ∅) as "Hclo''".
    { set_solver. }
    iMod "H". iModIntro. iNext. iModIntro.
    iApply (step_fupdN_le (S k'')); [ auto | lia |].
    iApply (step_fupdN_wand with "H"). iIntros "H".
    iMod "H" as "(?&HP)".
    iMod "Hclo''" as "_".
    iMod ("Hclo'" $! P True%I false with "[HP]").
    { iFrame. iAlways.
      iIntros. eauto.
    }
    iApply step_fupdN_inner_later; auto.
    { set_solver+. }
Qed.

Lemma wpc_staged_inv_open' Γ s k k' k'' E1 E1' E2 e Φ Φc Q Qrest Qnew P N b bset :
  E1 ⊆ E1' →
  ↑N ⊆ E1 →
  k'' ≤ k →
  (2 * (S k'')) ≤ k' →
  (2 * (S k)) ≤ k' →
  to_val e = None →
  staged_inv Γ N k' (E1' ∖ ↑N) (E1' ∖ ↑N) ∗
  staged_bundle Γ Q Qrest b bset ∗
  (Φc ∧ (Q -∗ WPC e @ NotStuck; k''; (E1 ∖ ↑N); ∅ {{λ v, ▷ Qnew v ∗ ▷ □ (Qnew v -∗ P) ∗ (staged_bundle Γ (Qnew v) True false bset -∗  (Φc ∧ Φ v))}} {{ Φc ∗ ▷ P }})) ∗
  staged_crash Γ P bset
  ⊢
  WPC e @ s; (2 * (S (S (S k)))); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (????? Hval) "(#Hinv&Hval&Hwp&#Hstaged_crash)".
  rewrite !wpc_unfold /wpc_pre.
  iSplit; last first.
  {
    iDestruct "Hwp" as "(Hwp&_)". iIntros "HC".
    iApply step_fupdN_inner_later; try reflexivity.
    repeat iNext.
    iApply step_fupdN_inner_later; try reflexivity.
    { set_solver. }
    eauto.
  }
  rewrite Hval.
  iIntros (????) "Hstate HNC".
  iMod (staged_inv_open with "[$]") as "[(H&Hclo)|Hfalse]"; [ auto | auto | |];
    last first.
  { iDestruct "Hfalse" as "(_&HC&_)".
    iDestruct (NC_C with "[$] [$]") as "[]".
  }
  replace (S (2 * (S (S (S k))))) with (S (S (S (2 * (S (S k)))))); last first.
  { lia. }
  iMod (fupd_intro_mask' _ ∅) as "Hclo'"; first set_solver+.
  iModIntro.
  iEval (rewrite Nat_iter_S). iModIntro. iNext.
  iEval (rewrite Nat_iter_S). do 2 iModIntro. iNext.
  iEval (rewrite Nat_iter_S). do 2 iModIntro. iNext.
  iDestruct ("Hwp" with "[$]") as "(Hwp&_)".
  iMod "Hclo'".
  iMod ("Hwp" with "[$] [$]") as "Hwp". iModIntro.
  rewrite Nat_iter_add.
  iEval rewrite Nat_iter_S_r.
  iApply (step_fupdN_le (S k'')); [ auto | lia |].
  iApply (step_fupdN_wand with "Hwp").
  iIntros "Hwp".
  iModIntro. iNext. rewrite right_id. rewrite Nat_iter_S_r.
  iApply step_fupdN_inner_later; auto. iNext. iNext. iNext. iModIntro.
  iDestruct "Hwp" as "H".
  iMod "H". iModIntro.
  iDestruct "H" as "(%&H)".
  iSplitL "".
  { destruct s; eauto. }
  iIntros.
  iMod ("H" with "[//]") as "H".
  iEval rewrite Nat_iter_S.
  iModIntro. iModIntro. iNext.
  iEval rewrite Nat_iter_S.
  iModIntro. iModIntro. iNext.
  iEval rewrite Nat_iter_S.
  iModIntro. iModIntro. iNext.
  rewrite Nat_iter_add.
  iModIntro. iApply (step_fupdN_le (S k'')); try (auto; lia).
  iApply (step_fupdN_wand with "H"). iIntros "H".
  rewrite right_id.
  iEval rewrite Nat_iter_S.
  do 2 iMod "H". iModIntro. iNext.
  iMod "H".
  iMod "H".
  iModIntro. iApply (step_fupdN_le (S k'')); try (auto; lia).
  iApply (step_fupdN_wand with "H"). iIntros "H".
  iMod "H".
  iDestruct "H" as "(Hσ&H&Hefs&HNC)".
  iSpecialize ("Hclo" $!
                      (WPC e2 @ k''; E1 ∖ ↑N;∅
                        {{ v, ▷ Qnew v ∗ ▷□ (Qnew v -∗ P) ∗ (staged_bundle Γ (Qnew v) True false bset -∗ Φc ∧ Φ v) }}{{Φc ∗ ▷ P}})%I
               Φc true with "[H]").
  { iSplitL "H".
    - iNext. iFrame.
    - iAlways. iIntros "HC H".
    iPoseProof (wpc_crash with "H") as "H".
    iSpecialize ("H" with "[$]").
    iMod (fupd_intro_mask' _ (E1 ∖ ↑N)) as "Hclo".
    { set_solver. }
    iApply (step_fupdN_le (2 * S k)); eauto.
    replace (2 * (((S k)))) with (S k + S k) by lia.
    rewrite Nat_iter_add.
    iMod "H". iModIntro.
    iEval rewrite step_fupdN_S_fupd.
    iApply (step_fupdN_le (S k'')); try (auto; lia).
    iApply (step_fupdN_wand with "H").
    iIntros "HP".
    iMod "HP". iMod "Hclo".
    iApply (step_fupdN_inner_wand with "HP"); eauto.
    { set_solver+. }
    { lia. }
    iIntros "($&$)".
  }
  iMod "Hclo".
  iMod (fupd_intro_mask' _ ∅) as "Hclo''"; first by set_solver+.
  iModIntro. iModIntro. iNext. iMod "Hclo''" as "_".
  iModIntro.
  iPoseProof (wpc_staged_inv_open_aux' Γ s k k' k'' E1 E1'
                _ _ Φ Φc P Qnew N with "[Hclo HNC]") as "H"; try assumption.
  { iIntros. iFrame "Hinv". iFrame. eauto. }
  iApply (step_fupdN_inner_wand with "H"); auto.
  iIntros "(Hwp&?)". iFrame.
  iSplitL "Hwp".
  { iIntros. iApply (wpc_strong_mono' with "[$]"); eauto.
    - lia.
    - iSplit; first auto. iIntros. iApply fupd_mask_weaken; eauto; set_solver.
  }
  iApply (big_sepL_mono with "Hefs").
  iIntros. iApply (wpc_strong_mono' with "[$]"); eauto.
  - lia.
  - set_solver+.
  - iSplit; first auto. iIntros. iApply fupd_mask_weaken; eauto; set_solver.
Qed.


Lemma wpc_staged_inv_init'' Γ s k k' N E1 E2 e Φ Φc P i:
  S k' < k →
  2 < k →
  ↑N ⊆ E1 →
  staged_inv Γ N (k') (E1 ∖ ↑N) (E1 ∖ ↑N) ∗
  staged_crash_pending Γ P i ∗
  WPC e @ s; k; E1; E2 {{ Φ }} {{ Φc }} ⊢
  WPC e @ s; (2 * k); E1; E2 {{ Φ }} {{ Φc ∗ P }}.
Proof.
  iIntros (Hle Hin ?) "(#Hinv&Hpending&H)".
  destruct k as [|k]; first by lia.
  destruct k as [|k]; first by lia.
  iApply (wpc_staged_inv_init' with "[$]").
  - lia.
  - eauto.
Qed.

Lemma wpc_staged_inv_open'' Γ s k k' k'' E1 E1' E2 e Φ Φc Q Qrest Qnew P N b bset :
  E1 ⊆ E1' →
  ↑N ⊆ E1 →
  k'' ≤ k →
  (4 * k) ≤ k' →
  2 < k →
  to_val e = None →
  staged_inv Γ N k' (E1' ∖ ↑N) (E1' ∖ ↑N) ∗
  staged_bundle Γ Q Qrest b bset ∗
  staged_crash Γ P bset ∗
  (Φc ∧ (Q -∗ WPC e @ NotStuck; k''; (E1 ∖ ↑N); ∅ {{λ v, ▷ Qnew v ∗ ▷ □ (Qnew v -∗ P) ∗ (staged_bundle Γ (Qnew v) True false bset -∗  (Φc ∧ Φ v))}} {{ Φc ∗ ▷ P }})) ⊢
  WPC e @ s; (4 * k); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (??????) "(?&?&?&?)".
  destruct k as [|k]; first by lia.
  destruct k as [|k]; first by lia.
  replace (4 * (S (S k))) with (2 * (S (S (S (S (2 * k)))))) by lia.
  iApply (wpc_staged_inv_open' with "[-]"); last by iFrame.
  { eauto. }
  { eauto. }
  { lia. }
  { lia. }
  { lia. }
  { eauto. }
Qed.

Notation base := 4.
Definition LVL (k: nat) : nat := base ^ ((S (S k))).

Lemma wpc_staged_inv_init Γ s k k' N E1 E2 e Φ Φc P i :
  k' < k →
  ↑N ⊆ E1 →
  staged_inv Γ N (LVL k') (E1 ∖ ↑N) (E1 ∖ ↑N) ∗
  staged_crash_pending Γ P i ∗
  WPC e @ s; LVL k; E1; E2 {{ Φ }} {{ Φc }} ⊢
  WPC e @ s; LVL (S k); E1; E2 {{ Φ }} {{ Φc ∗ P }}.
Proof.
  rewrite /LVL. iIntros (??) "(?&?&?)".
  replace (base ^ (S (S (S k)))) with (base * (base ^ ((S (S k))))) by auto.
  iApply (wpc_idx_mono _ (2 * base ^ (S (S k)))).
  {  lia. }
  iApply wpc_staged_inv_init''; last first. iFrame; auto.
  - eauto.
  - transitivity (base)%nat; first by auto. replace base with (base^1) by auto. apply Nat.pow_lt_mono_r_iff; eauto => //=. lia.
    lia.
  - apply (lt_le_trans _ (base * (base ^ (S (S k'))))).
    cut (1 < base ^ (S (S k'))); try lia.
    { replace 1 with (base^0) by auto. apply Nat.pow_lt_mono_r_iff; lia. }
    rewrite -PeanoNat.Nat.pow_succ_r'. apply Nat.pow_le_mono_r_iff; lia.
Qed.

Lemma wpc_staged_inv_init_wand Γ s k k' N E1 E2 e Φ Φc P i :
  k' < k →
  ↑N ⊆ E1 →
  staged_inv Γ N (LVL k') (E1 ∖ ↑N) (E1 ∖ ↑N) ∗
  staged_crash_pending Γ P i ∗
  WPC e @ s; LVL k; E1; E2 {{ Φ }} {{ P -∗ Φc }} ⊢
  WPC e @ s; LVL (S k); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (??) "(Hstaged&Hcrash&Hwp)".
  iAssert (WPC e @ s; LVL (S k); E1; E2 {{ Φ }} {{ (P -∗ Φc) ∗ P }})%I with "[-]" as "Hwp"; last first.
  { iApply (wpc_mono with "Hwp"); auto. rewrite wand_elim_l //. }
  by iApply (wpc_staged_inv_init with "[$]").
Qed.

Lemma wpc_staged_inv_open Γ s k k' E1 E1' E2 e Φ Φc Q Qrest Qnew P N b bset :
  E1 ⊆ E1' →
  ↑N ⊆ E1 →
  S k < k' →
  to_val e = None →
  staged_inv Γ N (LVL k') (E1' ∖ ↑N) (E1' ∖ ↑N) ∗
  staged_bundle Γ Q Qrest b bset ∗
  staged_crash Γ P bset ∗
  (Φc ∧ ((Q) -∗ WPC e @ NotStuck; (LVL k); (E1 ∖ ↑N); ∅ {{λ v, ▷ Qnew v ∗ ▷ □ (Qnew v -∗ P) ∗ (staged_bundle Γ (Qnew v) True false bset -∗  (Φc ∧ Φ v))}} {{ Φc ∗ ▷ P }})) ⊢
  WPC e @ s; LVL ((S k)); E1; E2 {{ Φ }} {{ Φc }}.
Proof.
  rewrite /LVL. iIntros (????) "(?&?&?)".
  assert (Hpow: base ^ (S (S (S k))) =  4 * base ^ (S (S k))).
  { rewrite //=. }
  rewrite Hpow.
  iApply (wpc_idx_mono _ (4 * base ^ (S (S k)))).
  { lia. }
  iApply (wpc_staged_inv_open'' with "[$]"); eauto.
  { transitivity (4 * base ^ (S (S k))); first by lia. rewrite -Hpow. apply Nat.pow_le_mono_r_iff; eauto. lia. }
  { transitivity (base)%nat; first lia. replace base with (base^1) at 1; last by auto.
    apply Nat.pow_lt_mono_r_iff; eauto. lia. }
Qed.

Lemma LVL_le k k':
  k ≤ k' →
  LVL k ≤ LVL k'.
Proof.
  rewrite /LVL => ?. apply Nat.pow_le_mono_r_iff; auto. lia.
Qed.

Lemma SSS_LVL k:
  (S (S (S (LVL k)))) ≤ LVL (S k).
Proof.
  rewrite /LVL.
  rewrite {1}(Nat.pow_succ_r' base (S (S k))).
  replace (S (S (S (base ^ (S (S k)))))) with (3 + (base^(S (S k)))); last by lia.
  replace (2 * (base ^ (S (S k)))) with (base ^ (S (S k)) + (base ^ (S (S k)))) by lia.
  apply plus_le_compat; auto.
  { transitivity (base)%nat; first lia. replace base with (base^1) at 1; last by auto.
  apply Nat.pow_le_mono_r_iff; eauto. lia. }
  lia.
Qed.

Lemma SS_LVL k:
  S (S (LVL k)) ≤ LVL (S k).
Proof.
  etransitivity; last eapply SSS_LVL; eauto.
Qed.

Lemma wpc_later' s k E1 E2 e Φ Φc :
  to_val e = None →
  ▷ ▷ WPC e @ s; (LVL k); E1 ; E2 {{ Φ }} {{ Φc }} -∗
  WPC e @ s; (LVL (S k)); E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "Hwp".
  pose proof (SS_LVL k).
  iApply (wpc_idx_mono with "[Hwp]"); first by eassumption.
  iApply (wpc_later with "[Hwp]"); eauto.
  iNext.
  iApply (wpc_later with "[Hwp]"); eauto.
Qed.

Lemma wpc_later_crash' s k E1 E2 e Φ Φc :
  WPC e @ s; (LVL k); E1 ; E2 {{ Φ }} {{ ▷ ▷ Φc }} -∗
  WPC e @ s; (LVL (S k)); E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "Hwp".
  pose proof (SS_LVL k).
  iApply (wpc_idx_mono with "[Hwp]"); first by eassumption.
  iApply (wpc_later_crash with "[Hwp]"); eauto.
  iApply (wpc_later_crash with "[Hwp]"); eauto.
Qed.

Lemma wpc_step_fupd' s k E1 E2 e Φ Φc :
  to_val e = None →
  (|={E1,∅}▷=> WPC e @ s; (LVL k); E1 ; E2 {{ Φ }} {{ Φc }}) -∗
  WPC e @ s; (LVL (S k)); E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "Hwp".
  specialize (SS_LVL k) => Hlvl.
  assert (S (LVL k) ≤ LVL (S k)) by lia.
  clear Hlvl.
  iApply (wpc_idx_mono with "[Hwp]"); first by eassumption.
  iApply (wpc_step_fupd with "[Hwp]"); eauto.
Qed.

Lemma wpc_step_fupdN_inner3 s k E1 E2 e Φ Φc :
  to_val e = None →
  (|={E1,E1}_3=> WPC e @ s; (LVL k); E1 ; E2 {{ Φ }} {{ Φc }}) -∗
  WPC e @ s; (LVL (S k)); E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "Hwp".
  specialize (SSS_LVL k) => Hlvl.
  iApply (wpc_idx_mono with "[Hwp]"); first by eassumption.
  replace (S (S (S (LVL k)))) with (3 + LVL k) by lia.
  iApply (wpc_step_fupdN_inner with "[Hwp]"); eauto.
Qed.

Lemma wpc_step_fupdN_inner3_NC s k E1 E2 e Φ Φc :
  to_val e = None →
  Φc ∧ (NC -∗ |={E1,E1}_3=> NC ∗ WPC e @ s; (LVL k); E1 ; E2 {{ Φ }} {{ Φc }}) -∗
  WPC e @ s; (LVL (S k)); E1 ; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (?) "Hwp".
  specialize (SSS_LVL k) => Hlvl.
  iApply (wpc_idx_mono with "[Hwp]"); first by eassumption.
  replace (S (S (S (LVL k)))) with (3 + LVL k) by lia.
  iApply (wpc_step_fupdN_inner_NC with "[Hwp]"); eauto.
  iApply (and_mono with "Hwp"); auto.
  iIntros. by iApply intro_cfupd.
Qed.

Lemma wpc_fupd_crash_shift_empty' s k E1 e Φ Φc :
  WPC e @ s; (LVL k) ; E1 ; ∅ {{ Φ }} {{ |={E1}=> Φc }} ⊢ WPC e @ s; LVL (S k); E1 ; ∅ {{ Φ }} {{ Φc }}.
Proof.
  iApply wpc_fupd_crash_shift_empty.
  rewrite /LVL.
  cut (2 * base ^ (S (S k)) + 1 ≤ base ^ (S (S (S k)))); first lia.
  assert (Hpow: base ^ ((S (S (S k)))) =  base * base ^ (S (S k))).
  { rewrite //=. }
  rewrite Hpow.
  cut (1 ≤ base ^ (S (S k))); first lia.
  replace 1 with (base^0) by auto. apply Nat.pow_le_mono_r_iff; eauto. lia.
Qed.

End staged_inv_wpc.
