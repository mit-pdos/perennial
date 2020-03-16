From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export step_fupd_extra crash_token crash_lang crash_weakestpre.
Import uPred.
Import language.

Set Default Proof Using "Type".

Section crash_adequacy.
Context `{!irisG Λ Σ, crashG Σ}.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation wptp s k t := ([∗ list] ef ∈ t, WPC ef @ s; k; ⊤; ⊤ {{ fork_post }} {{ True }})%I.

Lemma wpc_step s k e1 σ1 κ κs e2 σ2 efs m Φ Φc :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 (κ ++ κs) m -∗ WPC e1 @ s; k; ⊤; ⊤ {{ Φ }} {{ Φc }} -∗ NC -∗
  |={⊤,⊤}_(3 * (S (S k)))=>
  state_interp σ2 κs (length efs + m) ∗
  WPC e2 @ s; k; ⊤; ⊤ {{ Φ }} {{ Φc }} ∗
  wptp s k efs ∗
  NC.
Proof.
  rewrite {1}wpc_unfold /wpc_pre. iIntros (?) "Hσ H HNC".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iDestruct "H" as "(H&_)".
  replace (3 * S (S k)) with (S (S k) + S (S k) + S (S k)) by lia.
  rewrite Nat_iter_add Nat_iter_add Nat_iter_S.
  iMod ("H" $! σ1 with "Hσ HNC") as "H".
  do 4 iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "H". rewrite Nat_iter_S.
  iMod "H" as "(_ & H)".
  iMod ("H" $! e2 σ2 efs with "[//]") as "H".
  iIntros "!> !> !>".
  iApply (step_fupdN_wand with "H"). iIntros "H".
  iEval (rewrite Nat_iter_S). do 2 iMod "H". iModIntro. iNext.
  by iMod "H".
Qed.

Lemma wptp_step s k e1 t1 t2 κ κs σ1 σ2 Φ Φc :
  step (e1 :: t1,σ1) κ (t2, σ2) →
  state_interp σ1 (κ ++ κs) (length t1) -∗ WPC e1 @ s; k; ⊤; ⊤ {{ Φ }} {{ Φc }}-∗ wptp s k t1 -∗ NC ==∗
  ∃ e2 t2', ⌜t2 = e2 :: t2'⌝ ∗
  |={⊤,⊤}_(3 * (S (S k)))=> state_interp σ2 κs (pred (length t2)) ∗ WPC e2 @ s; k; ⊤; ⊤ {{ Φ }} {{ Φc}} ∗ wptp s k t2' ∗ NC.
Proof.
  iIntros (Hstep) "Hσ He Ht HNC".
  destruct Hstep as [e1' σ1' e2' σ2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', (t2' ++ efs). iModIntro. iSplitR; first by eauto.
    iMod (wpc_step with "Hσ He HNC") as "H"; first done.
    iApply (step_fupdN_wand with "H"). iModIntro. iIntros "H".
    iMod "H" as "(Hσ & He2 & Hefs & HNC)".
    iIntros "!>". rewrite Nat.add_comm app_length. iFrame.
  - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
    iDestruct "Ht" as "(Ht1 & He1 & Ht2)".
    iModIntro. iMod (wpc_step with "Hσ He1 HNC") as "H"; first done.
    iApply (step_fupdN_wand with "H"). iModIntro. iIntros "H".
    iMod "H" as "(Hσ & He2 & Hefs & HNC)". iIntros "!>".
    iFrame "He". rewrite !app_length /= !app_length.
    replace (length t1' + S (length t2' + length efs))
      with (length efs + (length t1' + S (length t2'))) by omega. iFrame.
Qed.

Lemma wptp_steps s k n e1 t1 κs κs' t2 σ1 σ2 Φ Φc :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗ WPC e1 @ s; k; ⊤; ⊤ {{ Φ }} {{ Φc }} -∗ wptp s k t1 -∗ NC -∗
  |={⊤,⊤}_(3 * (S (S k)))=>^n (∃ e2 t2',
    ⌜t2 = e2 :: t2'⌝ ∗
    state_interp σ2 κs' (pred (length t2)) ∗
    WPC e2 @ s; k; ⊤; ⊤ {{ Φ }} {{ Φc }} ∗ wptp s k t2' ∗
    NC).
Proof.
  revert e1 t1 κs κs' t2 σ1 σ2; simpl.
  induction n as [|n IH]=> e1 t1 κs κs' t2 σ1 σ2 /=.
  { inversion_clear 1; iIntros "????"; iExists e1, t1; iFrame; eauto 10. }
  iIntros (Hsteps) "Hσ He Ht HNC". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite -(assoc_L (++)).
  iMod (wptp_step with "Hσ He Ht HNC") as (e1' t1'' ?) ">H"; first eauto; simplify_eq.
  iApply (step_fupdN_wand with "H"). iModIntro. iIntros "H".
  iMod "H" as "(Hσ & He & Ht & HNC)". iIntros "!>".
  by iApply (IH with "Hσ He Ht HNC").
Qed.

Lemma wpc_safe E k κs m e σ Φ Φc :
  state_interp σ κs m -∗
  WPC e @ k ; ⊤ ; E {{ Φ }} {{ Φc }} -∗ NC ={⊤}=∗ ▷^(S (S k))
  ⌜is_Some (to_val e) ∨ reducible e σ⌝.
Proof.
  rewrite wpc_unfold /wpc_pre. iIntros "Hσ (H&_) HNC".
  destruct (to_val e) as [v|] eqn:?; first by eauto.
  iSpecialize ("H" $! σ [] κs with "Hσ HNC").
  iMod (step_fupdN_inner_plain with "[H]") as "H".
  2: { iMod "H". iApply (step_fupdN_wand with "H").
       iModIntro. iIntros "H". iMod "H" as "(H&_)".
       iApply "H". }
  { apply _. }
  iModIntro; eauto.
  repeat iNext; iDestruct "H" as %?; eauto.
Qed.

Lemma wptp_strong_adequacy Φ Φc k κs' s n e1 t1 κs t2 σ1 σ2 :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WPC e1 @ s; k; ⊤; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗
  NC -∗
  |={⊤,⊤}_(3 * (S (S k)))=>^(S n) (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC).
Proof.
  iIntros (Hstep) "Hσ He Ht HNC". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps with "Hσ He Ht HNC") as "Hwp"; first done.
  iApply (step_fupdN_innerN_wand with "Hwp"); auto.
  iDestruct 1 as (e2' t2' ?) "(Hσ & Hwp & Ht & HNC)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    (▷^(S (S k)) ⌜ ∀ e2, s = NotStuck → e2 ∈ (e2' :: t2') → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝)%I
    (state_interp σ2 κs' (length t2') ∗ WPC e2' @ s; k; ⊤; ⊤ {{ v, Φ v }} {{ Φc }} ∗ wptp s k t2' ∗ NC)%I
    with "[$Hσ $Hwp $Ht $HNC]") as "(Hsafe&Hσ&Hwp&Hvs&HNC)".
  { iIntros "(Hσ & Hwp & Ht & HNC)" (e' -> He').
    apply elem_of_cons in He' as [<-|(t1''&t2''&->)%elem_of_list_split].
    - iMod (wpc_safe with "Hσ Hwp HNC") as "$"; auto.
    - iDestruct "Ht" as "(_ & He' & _)". by iMod (wpc_safe with "Hσ He' HNC"). }
  iApply step_fupd_fupd. iApply step_fupd_intro; first done.
  iMod (fupd_intro_mask' _ ∅) as "Hclo". auto.
  do 5 (iModIntro). iMod "Hclo".
  iApply step_fupdN_inner_fupd.
  iApply (step_fupdN_inner_later); auto.
  iNext.
  iExists _, _. iSplitL ""; first done. iFrame "Hsafe Hσ".
  iMod (wpc_value_inv_option with "Hwp HNC") as "($&HNC)".
  clear Hstep. iInduction t2' as [|e t2'] "IH"; csimpl; first by iFrame.
  iDestruct "Hvs" as "[Hv Hvs]". destruct (to_val e) as [v|] eqn:He.
  + apply of_to_val in He as <-. iMod (wpc_value_inv' with "Hv HNC") as "($&?)".
    by iApply ("IH" with "[$] [$] [$]").
  + by iApply ("IH" with "[$] [$] [$]").
Qed.

Lemma wptp_strong_crash_adequacy Φ Φc κs' s k n e1 t1 κs t2 σ1 σ2 :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WPC e1 @ s; k; ⊤; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗
  NC -∗ |={⊤,⊤}_(3 * S (S k))=>^(S n) |={⊤,⊤}_(S k)=> |={⊤, ∅}_(S k)=> (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    Φc ∗ state_interp σ2 κs' (length t2') ∗ C).
Proof.
  iIntros (Hstep) "Hσ He Ht HNC". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps with "Hσ He Ht HNC") as "Hwp"; first done.
  iApply (step_fupdN_innerN_wand with "Hwp"); auto.
  iDestruct 1 as (e2' t2' ?) "(Hσ & Hwp & Ht & HNC)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    (▷^(S (S k)) ⌜ ∀ e2, s = NotStuck → e2 ∈ (e2' :: t2') → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝)%I
    (state_interp σ2 κs' (length t2') ∗ WPC e2' @ s; k; ⊤; ⊤ {{ v, Φ v }} {{ Φc }} ∗ wptp s k t2' ∗ NC)%I
    with "[$Hσ $Hwp $Ht $HNC]") as "(Hsafe&Hσ&Hwp&Hvs&HNC)".
  { iIntros "(Hσ & Hwp & Ht & HNC)" (e' -> He').
    apply elem_of_cons in He' as [<-|(t1''&t2''&->)%elem_of_list_split].
    - iMod (wpc_safe with "Hσ Hwp HNC") as "$"; auto.
    - iDestruct "Ht" as "(_ & He' & _)". by iMod (wpc_safe with "Hσ He' HNC"). }
  iApply step_fupd_fupd. iApply step_fupd_intro; first done.
  iMod (fupd_intro_mask' _ ∅) as "Hclo". auto.
  do 5 (iModIntro). iMod "Hclo".
  iApply step_fupdN_inner_fupd.
  iApply (step_fupdN_inner_later); auto.
  iNext. iModIntro.
  iMod (NC_upd_C with "HNC") as "#HC".
  iMod (wpc_crash with "Hwp HC") as "H".
  iModIntro.
  iApply (step_fupdN_wand _ _ (S k) with "H [-]"); eauto.
  iIntros "H". iMod "H". iModIntro.
  iApply (step_fupdN_inner_wand' _ _ _ _ (S k) with "H [-]"); eauto.
  iIntros "HΦ". iExists _, _; iFrame; eauto.
Qed.
End crash_adequacy.
