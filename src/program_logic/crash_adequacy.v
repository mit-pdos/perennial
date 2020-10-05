From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export step_fupd_extra crash_lang crash_weakestpre.
Import uPred.
Import language.

Set Default Proof Using "Type".

Section crash_adequacy.
Context `{!irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Context (mj: nat).
(* The IH of the theorems here requires working with some fixed choice of mj in the wpc0 form,
   instead of wpc. So, we introduce here a notation to insert the mj explicitly to porting these proofs easier *)
Local Notation "'WPC' e @ k ; E1 {{ Φ } } {{ Φc } }" := (wpc0 NotStuck k%nat mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Local Notation "'WPC' e @ s ; k ; E1 {{ Φ } } {{ Φc } }" := (wpc0 s k%nat mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Local Notation "'WPC' e @ s ; k ; E1 {{ Φ } } {{ Φc } }" := (wpc0 s k%nat mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : stdpp_scope.

Notation wptp s k t := ([∗ list] ef ∈ t, WPC ef @ s; k; ⊤ {{ fork_post }} {{ True }})%I.

Lemma wpc_step s k e1 σ1 κ κs e2 σ2 efs m Φ Φc :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 (κ ++ κs) m -∗ WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗ NC 1 -∗
  |={⊤}[∅]▷=>
  state_interp σ2 κs (length efs + m) ∗
  WPC e2 @ s; k; ⊤ {{ Φ }} {{ Φc }} ∗
  wptp s k efs ∗
  NC 1.
Proof.
  rewrite {1}wpc0_unfold /wpc_pre. iIntros (?) "Hσ H HNC".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iMod "H". iDestruct "H" as "(H&_)".
  iMod ("H" $! _ σ1 with "Hσ HNC") as "(_&H)".
  iMod ("H" $! e2 σ2 efs with "[//]") as "H".
  do 2 iModIntro. by iMod "H" as "($&$&?&$)".
Qed.

Lemma wptp_step s k e1 t1 t2 κ κs σ1 σ2 Φ Φc :
  step (e1 :: t1,σ1) κ (t2, σ2) →
  state_interp σ1 (κ ++ κs) (length t1) -∗ WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }}-∗ wptp s k t1 -∗ NC 1 ==∗
  ∃ e2 t2', ⌜t2 = e2 :: t2'⌝ ∗
  |={⊤}[∅]▷=> state_interp σ2 κs (pred (length t2)) ∗ WPC e2 @ s; k; ⊤ {{ Φ }} {{ Φc}} ∗ wptp s k t2' ∗ NC 1.
Proof.
  iIntros (Hstep) "Hσ He Ht HNC".
  destruct Hstep as [e1' σ1' e2' σ2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', (t2' ++ efs). iModIntro. iSplitR; first by eauto.
    iMod (wpc_step with "Hσ He HNC") as "H"; first done.
    iIntros "!> !>". iMod "H" as "(Hσ & He2 & Hefs)".
    iIntros "!>". rewrite Nat.add_comm app_length. by iFrame.
  - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
    iDestruct "Ht" as "(Ht1 & He1 & Ht2)".
    iModIntro. iMod (wpc_step with "Hσ He1 HNC") as "H"; first done.
    iIntros "!> !>". iMod "H" as "(Hσ & He2 & Hefs)". iIntros "!>".
    rewrite !app_length /= !app_length.
    replace (length t1' + S (length t2' + length efs))
      with (length efs + (length t1' + S (length t2'))) by lia. by iFrame.
Qed.

Lemma wptp_steps s k n e1 t1 κs κs' t2 σ1 σ2 Φ Φc :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗ WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗ wptp s k t1 -∗ NC 1 -∗
  |={⊤}[∅]▷=>^n (∃ e2 t2',
    ⌜t2 = e2 :: t2'⌝ ∗
    state_interp σ2 κs' (pred (length t2)) ∗
    WPC e2 @ s; k; ⊤ {{ Φ }} {{ Φc }} ∗ wptp s k t2' ∗
    NC 1).
Proof.
  revert e1 t1 κs κs' t2 σ1 σ2; simpl.
  induction n as [|n IH]=> e1 t1 κs κs' t2 σ1 σ2 /=.
  { inversion_clear 1; iIntros "????"; iExists e1, t1; iFrame; eauto 10. }
  iIntros (Hsteps) "Hσ He Ht HNC". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite -(assoc_L (++)).
  iMod (wptp_step with "Hσ He Ht HNC") as (e1' t1'' ?) ">H"; first eauto; simplify_eq.
  iIntros "!> !>". iMod "H" as "(Hσ & He & Ht & HNC)". iModIntro.
  by iApply (IH with "Hσ He Ht HNC").
Qed.

Lemma wpc_safe k κs m e σ Φ Φc :
  state_interp σ κs m -∗
  WPC e @ k ; ⊤  {{ Φ }} {{ Φc }} -∗ NC 1 ={⊤}=∗
  ⌜is_Some (to_val e) ∨ reducible e σ⌝.
Proof.
  rewrite wpc0_unfold /wpc_pre. iIntros "Hσ H HNC". iDestruct "H" as ">(H&_)".
  destruct (to_val e) as [v|] eqn:?; first by eauto.
  iSpecialize ("H" $! _ σ [] κs with "Hσ HNC"). rewrite sep_elim_l.
  iMod (fupd_plain_mask with "H") as %?; eauto.
Qed.

Lemma wptp0_strong_adequacy Φ Φc k κs' s n e1 t1 κs t2 σ1 σ2 :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗
  NC 1 -∗
  |={⊤}[∅]▷=>^(S n) (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1).
Proof.
  iIntros (Hstep) "Hσ He Ht HNC". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps with "Hσ He Ht HNC") as "Hwp"; first done.
  iApply (step_fupdN_wand with "Hwp").
  iDestruct 1 as (e2' t2' ?) "(Hσ & Hwp & Ht & HNC)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    (⌜ ∀ e2, s = NotStuck → e2 ∈ (e2' :: t2') → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝)%I
    (state_interp σ2 κs' (length t2') ∗
     wpc0 s k mj ⊤ e2' Φ Φc ∗ wptp s k t2' ∗ NC 1)%I
    with "[$Hσ $Hwp $Ht $HNC]") as "(Hsafe&Hσ&Hwp&Hvs&HNC)".
  { iIntros "(Hσ & Hwp & Ht & HNC)" (e' -> He').
    apply elem_of_cons in He' as [<-|(t1''&t2''&->)%elem_of_list_split].
    - iMod (wpc_safe with "Hσ Hwp HNC") as "$"; auto.
    - iDestruct "Ht" as "(_ & He' & _)". by iMod (wpc_safe with "Hσ He' HNC"). }
  iApply step_fupd_fupd. iApply step_fupd_intro; first done. iNext.
  iExists _, _. iSplitL ""; first done. iFrame "Hsafe Hσ".
  iMod (wpc0_value_inv_option with "Hwp HNC") as "($&HNC)".
  clear Hstep. iInduction t2' as [|e t2'] "IH"; csimpl; first by iFrame.
  iDestruct "Hvs" as "[Hv Hvs]". destruct (to_val e) as [v|] eqn:He.
  + apply of_to_val in He as <-. iMod (wpc0_value_inv' with "Hv HNC") as "($&?)".
    by iApply ("IH" with "[$] [$]").
  + by iApply ("IH" with "[$] [$]").
Qed.

Lemma wptp0_strong_crash_adequacy Φ Φc κs' s k n e1 t1 κs t2 σ1 σ2 :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗
  NC 1 -∗
  |={⊤}[∅]▷=>^(S n) |={⊤,∅}=> ▷ (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    Φc ∗ state_interp σ2 κs' (length t2') ∗ C).
Proof.
  iIntros (Hstep) "Hσ He Ht HNC". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps with "Hσ He Ht HNC") as "Hwp"; first done.
  iApply (step_fupdN_wand with "Hwp"); auto.
  iDestruct 1 as (e2' t2' ?) "(Hσ & Hwp & Ht & HNC)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    (⌜ ∀ e2, s = NotStuck → e2 ∈ (e2' :: t2') → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝)%I
    (state_interp σ2 κs' (length t2') ∗
     wpc0 s k mj ⊤ e2' Φ Φc ∗ wptp s k t2' ∗ NC 1)%I
    with "[$Hσ $Hwp $Ht $HNC]") as "(Hsafe&Hσ&Hwp&Hvs&HNC)".
  { iIntros "(Hσ & Hwp & Ht & HNC)" (e' -> He').
    apply elem_of_cons in He' as [<-|(t1''&t2''&->)%elem_of_list_split].
    - iMod (wpc_safe with "Hσ Hwp HNC") as "$"; auto.
    - iDestruct "Ht" as "(_ & He' & _)". by iMod (wpc_safe with "Hσ He' HNC"). }
  iApply step_fupd_fupd. iApply step_fupd_intro; first done. iNext.
  iMod (NC_upd_C with "HNC") as "#HC".
  iMod (wpc0_crash with "Hwp") as "H".
  iMod (own_disc_fupd_elim with "H") as "H".
  iModIntro.
  iSpecialize ("H" with "[$]").
  iMod (fupd_split_level_fupd with "H") as "H".
  iApply fupd_mask_weaken; first by set_solver.
  iNext.
  iExists _, _. iSplitL ""; first done. iFrame "# ∗".
Qed.
End crash_adequacy.

Section crash_adequacy.
Context `{!irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

(* Now we prove a version where we use normal wpc instead of wpc0. *)

Notation wptp s k t := ([∗ list] ef ∈ t, WPC ef @ s; k; ⊤ {{ fork_post }} {{ True }})%I.
Lemma wptp_strong_adequacy Φ Φc k κs' s n e1 t1 κs t2 σ1 σ2 :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗
  NC 1 -∗
  |={⊤}[∅]▷=>^(S n) (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1).
Proof.
  iIntros (?) "? Hwpc Hwptp Hnc".
  iApply (wptp0_strong_adequacy 0 with "[$] [Hwpc] [Hwptp] [$]"); first eassumption.
  { by iApply wpc0_wpc. }
  { iApply (big_sepL_mono with "Hwptp"). iIntros.
    iApply (wpc0_wpc); eauto.
  }
Qed.

Lemma wptp_strong_crash_adequacy Φ Φc κs' s k n e1 t1 κs t2 σ1 σ2 :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗
  NC 1 -∗
  |={⊤}[∅]▷=>^(S n) |={⊤,∅}=> ▷ (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    Φc ∗ state_interp σ2 κs' (length t2') ∗ C).
Proof.
  iIntros (?) "? Hwpc Hwptp Hnc".
  iApply (wptp0_strong_crash_adequacy 0 with "[$] [Hwpc] [Hwptp] [$]"); first eassumption.
  { by iApply wpc0_wpc. }
  { iApply (big_sepL_mono with "Hwptp"). iIntros.
    iApply (wpc0_wpc); eauto.
  }
Qed.

End crash_adequacy.
