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

Lemma staged_inv_init_cfupd' Γ k k' N E1 P i:
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
  iApply (staged_inv_init_cfupd'); eauto.
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

Lemma staged_inv_init_cfupd'' Γ k k' N E1 P i:
  S k' < k →
  2 < k →
  ↑N ⊆ E1 →
  staged_inv Γ N (k') (E1 ∖ ↑N) (E1 ∖ ↑N) ∗
  staged_crash_pending Γ P i -∗
  |C={E1, ∅}_(k)=> P.
Proof.
  iIntros (Hle Hin ?) "(#Hinv&Hpending&H)".
  destruct k as [|k]; first by lia.
  destruct k as [|k]; first by lia.
  iApply (staged_inv_init_cfupd' with "[$]").
  - lia.
  - eauto.
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

Lemma abstract_4k k :
  ∃ m, 4^k = m ∧ 1<=m.
Proof.
  eexists; split; eauto.
  induction k; simpl; lia.
Qed.

Lemma abstract_4k' k :
  ∃ m, 4^k = m ∧ 1≤m ∧ k<m.
Proof.
  eexists; split; eauto.
  induction k; simpl; lia.
Qed.

Tactic Notation "abstract_pow4" constr(k) :=
  let m := fresh "m" in
  destruct (abstract_4k' k) as [m [-> ?]]; nia.

Ltac abstract_some_pow4 :=
  match goal with
  | |- context[Nat.pow 4 ?k] => abstract_pow4 k
  end.

Tactic Notation "abstract_pow4" := abstract_some_pow4.

Lemma LVL_pow k : LVL k = 16 * 4^k.
Proof.
  rewrite /LVL /=.
  lia.
Qed.

Lemma LVL_gt k : k < LVL k.
Proof.
  rewrite /LVL.
  induction k; simpl.
  - lia.
  - abstract_pow4.
Qed.

Lemma LVL_le k k':
  k ≤ k' →
  LVL k ≤ LVL k'.
Proof.
  rewrite /LVL => ?. apply Nat.pow_le_mono_r_iff; auto. lia.
Qed.

Lemma LVL_mult k1 k2 :
  LVL k1 * LVL k2 = base*base * LVL (k1 + k2).
Proof.
  rewrite !LVL_pow.
  rewrite Nat.pow_add_r.
  lia.
Qed.

Lemma LVL_sum_bound k1 k2 :
  LVL (k1+k2) ≤ LVL k1 * LVL k2.
Proof.
  rewrite LVL_mult.
  lia.
Qed.

Lemma LVL_Sk k :
  LVL (S k) = base*LVL k.
Proof.
  rewrite /LVL /=.
  lia.
Qed.

Lemma LVL_mult_eq' k1 k2 :
  LVL k1 * LVL k2 = LVL (S (S (k1 + k2))).
Proof.
  rewrite LVL_mult !LVL_Sk.
  lia.
Qed.

Lemma base_le_LVL_S k:
  base + LVL k ≤ LVL (S k).
Proof.
  rewrite /LVL.
  simpl.
  abstract_pow4.
Qed.

Lemma SSS_LVL k:
  (S (S (S (LVL k)))) ≤ LVL (S k).
Proof.
  etransitivity; [ | apply base_le_LVL_S ].
  lia.
Qed.

Lemma SS_LVL k:
  S (S (LVL k)) ≤ LVL (S k).
Proof.
  etransitivity; [ | apply base_le_LVL_S ].
  lia.
Qed.

Lemma staged_inv_init_cfupd Γ k k' N E1 P i:
  k' < k →
  ↑N ⊆ E1 →
  staged_inv Γ N (LVL k') (E1 ∖ ↑N) (E1 ∖ ↑N) ∗
  staged_crash_pending Γ P i -∗
  |C={E1, ∅}_(LVL k)=> P.
Proof.
  rewrite /LVL.
  iIntros (Hle Hin)  "(#Hinv&Hpending)".
  iIntros "HΦc".
  iApply (staged_inv_init_cfupd'' with "[$] [$]"); auto.
  - apply (lt_le_trans _ (base * (base ^ (S (S k'))))).
    cut (1 < base ^ (S (S k'))); try lia.
    { replace 1 with (base^0) by auto. apply Nat.pow_lt_mono_r_iff; lia. }
    rewrite -PeanoNat.Nat.pow_succ_r'. apply Nat.pow_le_mono_r_iff; lia.
  - transitivity (base)%nat; first by auto. replace base with (base^1) by auto.
    apply Nat.pow_lt_mono_r_iff; eauto => //=; lia.
Qed.

Lemma wpc_crash_frame_wand' s k k' E E' Ec e Φ Φc Ψc :
  k' ≤ k → E' ⊆ E →
  (|C={E', ∅}_(LVL k')=> Ψc) -∗
  WPC e @ s; (LVL k); E ; Ec {{ Φ }} {{ Ψc -∗ Φc }} -∗
  WPC e @ s; (LVL (S k)); E ; Ec {{ Φ }} {{ Φc }}.
Proof.
  rewrite /LVL. iIntros (??) "Hc Hwpc".
  iApply (wpc_crash_frame_wand with "[$] [Hc]").
  apply Nat.pow_le_mono_r_iff; lia.
  iApply (cfupd_wand with "Hc"); auto.
  replace (base ^ (S (S (S k)))) with (base * (base ^ ((S (S k))))) by auto.
  transitivity (base ^ (S (S k))).
  { apply Nat.pow_le_mono_r_iff; lia. }
  lia.
Qed.

(* TODO: double-check that this special case actually fires *)
Global Instance elim_modal_cfupd_lvl p s k k' E1 E2 e P Φ Φc :
  ElimModal (k' ≤ k)%nat p false (cfupd (LVL k') E1 ∅ P) True
            (WPC e @ s; LVL (S k); E1; E2 {{ Φ }} {{ Φc }})
            (WPC e @ s; LVL k; E1; E2 {{ Φ }} {{ P -∗ Φc }}).
Proof.
  rewrite /ElimModal intuitionistically_if_elim.
  iIntros (?) "[Hc Hwpc]".
  iSpecialize ("Hwpc" with "[//]").
  iApply (wpc_crash_frame_wand' with "Hc Hwpc"); auto.
Qed.

Lemma LVL_sum_split n m :
  LVL (n + m) = 4^n * LVL m.
Proof.
  rewrite /LVL.
  replace (S (S (n + m))) with (n + (S (S m))) by lia.
  rewrite Nat.pow_add_r.
  reflexivity.
Qed.

Lemma LVL_scale_weaken n k :
  n * LVL k ≤ LVL (n+k) - LVL k.
Proof.
  rewrite LVL_sum_split.
  replace (4^n * LVL k - LVL k) with ((4^n-1) * (LVL k)).
  { apply Nat.mul_le_mono_r.
    abstract_pow4. }
  rewrite Nat.mul_sub_distr_r; lia.
Qed.

Lemma cfupd_weaken_mult E1 E2 n k P :
  (|C={E1,E2}_(n * LVL k)=> P) -∗
  |C={E1,E2}_(LVL (n+k) - LVL k)=> P.
Proof.
  iIntros "H".
  iApply (cfupd_wand with "H"); auto.
  apply LVL_scale_weaken.
Qed.

Lemma wpc_crash_frame_wand_mult s n k E Ec e Φ Φc Ψc :
  (|C={E, ∅}_(n * LVL k)=> Ψc) -∗
  WPC e @ s; (LVL k); E ; Ec {{ Φ }} {{ Ψc -∗ Φc }} -∗
  WPC e @ s; (LVL (n + k)); E ; Ec {{ Φ }} {{ Φc }}.
Proof.
  iIntros "Hcfupd Hwpc".
  iApply (wpc_crash_frame_wand with "Hwpc").
  { apply LVL_le; lia. }
  iApply cfupd_weaken_mult; auto.
Qed.

Lemma cfupd_big_sepS `{Countable A} (σ: gset A)(P: A → iProp Σ) k E1  :
  ([∗ set] a ∈ σ, |C={E1, ∅}_(LVL k)=> P a) -∗
  |C={E1, ∅}_(LVL (size σ + k))=> ([∗ set] a ∈ σ, P a).
Proof.
  iIntros "H".
  iInduction σ as [| x σ ?] "IH" using set_ind_L.
  - iModIntro. iNext.
    rewrite big_sepS_empty //.
  - rewrite -> !big_sepS_union by set_solver.
    rewrite !big_sepS_singleton.
    iDestruct "H" as "(Hx & Hrest)".
    rewrite size_union; last by set_solver.
    rewrite size_singleton.
    iMod "Hx".
    { simpl.
      rewrite LVL_Sk.
      pose proof (LVL_gt (size σ+k)).
      rewrite LVL_sum_split.
      abstract_pow4. }
    iFrame "Hx".
    iMod ("IH" with "Hrest") as "Hrest".
    { change (1 + size σ + k) with (S (size σ + k)).
      rewrite LVL_Sk.
      pose proof (LVL_gt (size σ + k)).
      pose proof (LVL_le k (size σ + k)).
      nia. }
    iModIntro. iModIntro.
    iFrame.
Qed.

Lemma wpc_crash_frame_big_sepS_wand `{Countable A} (σ: gset A)(P: A → iProp Σ) k s E2 e Φ Φc  :
  ([∗ set] a ∈ σ, ∃ k', ⌜ k' ≤ k ⌝ ∗ |C={⊤, ∅}_(LVL k')=> P a) -∗
  WPC e @ s; LVL k; ⊤; E2 {{ Φ }} {{ ([∗ set] a ∈ σ, P a) -∗ Φc }} -∗
  WPC e @ s; LVL (S k + size σ); ⊤; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros "Hs Hwpc".
  iDestruct (cfupd_big_sepS with "[Hs]") as "Hs".
  { iApply (big_sepS_mono with "Hs").
    iIntros (x ?) "H".
    iDestruct "H" as (k') "[% H]".
    iApply (cfupd_weaken_all _ (LVL k) with "H"); auto.
    apply LVL_le; auto. }
  simpl.
  iMod "Hs" as "_".
  { lia. }
  iApply (wpc_idx_mono with "Hwpc").
  apply LVL_le; lia.
Qed.

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
