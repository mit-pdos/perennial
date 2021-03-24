From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
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

Lemma wpc_step s k e1 σ1 g1 ns κ κs e2 σ2 g2 efs m Φ Φc :
  prim_step e1 σ1 g1 κ e2 σ2 g2 efs →
  state_interp σ1 m -∗
  global_state_interp g1 ns (κ ++ κs) -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗ NC 1 -∗
  |={⊤,∅}=> |={∅}▷=>^(S $ num_laters_per_step ns) |={∅,⊤}=>
  state_interp σ2 (length efs + m) ∗
  global_state_interp g2 (S ns) κs ∗
  WPC e2 @ s; k; ⊤ {{ Φ }} {{ Φc }} ∗
  wptp s k efs ∗
  NC 1.
Proof.
  rewrite {1}wpc0_unfold /wpc_pre. iIntros (?) "Hσ Hg H HNC".
  rewrite (val_stuck e1 σ1 g1 κ e2 σ2 g2 efs) //.
  iMod "H". iDestruct "H" as "(H&_)".
  iMod ("H" $! _ σ1 with "Hσ Hg HNC") as "H".
  iModIntro.
  iApply (step_fupdN_wand with "H"). iIntros "(_&H)".
  iMod ("H" $! e2 σ2 g2 efs with "[//]") as "H".
  iModIntro. eauto.
Qed.

Lemma wptp_step s k e1 t1 t2 κ κs σ1 g1 ns σ2 g2 Φ Φc :
  step (e1 :: t1,(σ1,g1)) κ (t2, (σ2,g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ns (κ ++ κs) -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }}-∗ wptp s k t1 -∗ NC 1 ==∗
  ∃ e2 t2', ⌜t2 = e2 :: t2'⌝ ∗
  |={⊤,∅}=> |={∅}▷=>^(S $ num_laters_per_step ns) |={∅,⊤}=>
  state_interp σ2 (pred (length t2)) ∗
  global_state_interp g2 (S ns) κs ∗
  WPC e2 @ s; k; ⊤ {{ Φ }} {{ Φc}} ∗ wptp s k t2' ∗ NC 1.
Proof.
  iIntros (Hstep) "Hσ Hg He Ht HNC".
  destruct Hstep as [e1' σ1' g1' e2' σ2' g2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', (t2' ++ efs). iModIntro. iSplitR; first by eauto.
    iMod (wpc_step with "Hσ Hg He HNC") as "H"; first done. iModIntro.
    iApply (step_fupdN_wand with "H"). iIntros ">(Hσ & Hg & He2 & Hefs) !>".
    rewrite Nat.add_comm app_length. by iFrame.
  - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
    iDestruct "Ht" as "(Ht1 & He1 & Ht2)".
    iModIntro. iMod (wpc_step with "Hσ Hg He1 HNC") as "H"; first done. iModIntro.
    iApply (step_fupdN_wand with "H"). iIntros ">(Hσ & Hg & He2 & Hefs) !>".
    rewrite !app_length /= !app_length.
    replace (length t1' + S (length t2' + length efs))
      with (length efs + (length t1' + S (length t2'))) by lia. by iFrame.
Qed.
(* The total number of laters used between the physical steps number
   [start] (included) to [start+ns] (excluded). *)
Local Fixpoint steps_sum (num_laters_per_step : nat → nat) (start ns : nat) : nat :=
  match ns with
  | O => 0
  | S ns =>
    S $ num_laters_per_step start + steps_sum num_laters_per_step (S start) ns
  end.

Lemma wptp_steps s k n e1 t1 κs κs' t2 σ1 g1 ns σ2 g2 Φ Φc :
  nsteps n (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ns (κs ++ κs') -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗ wptp s k t1 -∗ NC 1 -∗
  (|={⊤, ∅}=> |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅,⊤}=> ∃ e2 t2',
    ⌜t2 = e2 :: t2'⌝ ∗
    state_interp σ2 (pred (length t2)) ∗
    global_state_interp g2 (n + ns) κs' ∗
    WPC e2 @ s; k; ⊤ {{ Φ }} {{ Φc }} ∗ wptp s k t2' ∗
    NC 1).
Proof.
  revert e1 t1 κs κs' t2 σ1 g1 ns σ2 g2; simpl.
  induction n as [|n IH]=> e1 t1 κs κs' t2 σ1 g1 ns σ2 g2 /=.
  { inversion_clear 1; iIntros "?????"; iExists e1, t1; iFrame; eauto 10.
    iApply fupd_mask_intro_subseteq; eauto. }
  iIntros (Hsteps) "Hσ Hg He Ht HNC". inversion_clear Hsteps as [|?? [t1' [σ1' g1']]].
  rewrite -(assoc_L (++)) Nat_iter_add plus_n_Sm.
  iApply step_fupdN_S_fupd.
  iMod (wptp_step with "Hσ Hg He Ht HNC") as (e1' t1'' ?) ">H"; first eauto; simplify_eq.
  iApply (step_fupdN_wand with "H"). iIntros "!> H".
  iMod "H".
  iDestruct "H" as "(Hσ & Hg & He & Ht & HNC)".
  iMod (IH with "Hσ Hg He Ht HNC") as "IH"; first done.
  iModIntro. eauto.
Qed.

Lemma wpc_safe k κs m e σ g ns Φ Φc :
  state_interp σ m -∗
  global_state_interp g ns κs -∗
  WPC e @ k ; ⊤  {{ Φ }} {{ Φc }} -∗ |NC={⊤}=>
  ▷^(S (S (num_laters_per_step ns))) ⌜is_Some (to_val e) ∨ reducible e σ g⌝.
Proof.
  rewrite wpc0_unfold /wpc_pre. iIntros "Hσ Hg H". iDestruct "H" as ">(H&_)".
  destruct (to_val e) as [v|] eqn:?; first by eauto.
  iApply ncfupd_plain_fupd.
  iIntros (q) "HNC".
  iApply (step_fupdN_inner_plain (S (num_laters_per_step ns))).
  iMod ("H" $! _ _ _ _ [] with "[$] [$] [$]") as "H".
  simpl. iModIntro. iApply (step_fupdN_wand with "H").
  iNext. iIntros "(%&_)". eauto.
Qed.

Lemma wptp0_strong_adequacy Φ Φc k κs' s n e1 t1 κs t2 σ1 g1 ns σ2 g2 :
  nsteps n (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ns (κs ++ κs') -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗
  NC 1 -∗
  |={⊤,∅}=> |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅, ⊤}=> (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ▷^(S (S (num_laters_per_step (n + ns)))) (⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 g2 ⌝) ∗
    state_interp σ2 (length t2') ∗
    global_state_interp g2 (n + ns) κs' ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1).
Proof.
  iIntros (Hstep) "Hσ Hg He Ht HNC".
  iMod (wptp_steps with "Hσ Hg He Ht HNC") as "Hwp"; first done.
  iModIntro. iApply (step_fupdN_wand with "Hwp").
  iMod 1 as (e2' t2' ?) "(Hσ & Hg & Hwp & Ht & HNC)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    (▷^(S (S (num_laters_per_step (n + ns)))) ⌜ ∀ e2, s = NotStuck → e2 ∈ (e2' :: t2') → not_stuck e2 σ2 g2 ⌝)%I
    (state_interp σ2 (length t2') ∗
    (global_state_interp g2 (n + ns) κs') ∗
     wpc0 s k mj ⊤ e2' Φ Φc ∗ wptp s k t2' ∗ NC 1)%I
    with "[$Hσ $Hg $Hwp $Ht $HNC]") as "(Hsafe&Hσ&Hg&Hwp&Hvs&HNC)".
  { iIntros "(Hσ & Hg & Hwp & Ht & HNC)" (e' -> He').
    apply elem_of_cons in He' as [<-|(t1''&t2''&->)%elem_of_list_split].
    - iPoseProof (wpc_safe with "Hσ Hg Hwp") as "H".
      rewrite ncfupd_eq.
      by iMod ("H" with "[$]") as "($&_)".
    - iDestruct "Ht" as "(_ & He' & _)".
      iPoseProof (wpc_safe with "Hσ Hg He'") as "H".
      rewrite ncfupd_eq.
      by iMod ("H" with "[$]") as "($&_)". }
  iExists _, _. iSplitL ""; first done. iFrame "Hsafe Hσ".
  iMod (wpc0_value_inv_option with "Hwp HNC") as "($&HNC)".
  clear Hstep. iInduction t2' as [|e t2'] "IH"; csimpl; first by iFrame.
  iDestruct "Hvs" as "[Hv Hvs]". destruct (to_val e) as [v|] eqn:He.
  + apply of_to_val in He as <-. iMod (wpc0_value_inv' with "Hv HNC") as "($&?)".
    by iApply ("IH" with "[$] [$]").
  + by iApply ("IH" with "[$] [$]").
Qed.

Lemma wptp0_strong_crash_adequacy Φ Φc κs' s k n e1 t1 κs t2 σ1 g1 ns σ2 g2 :
  nsteps n (e1 :: t1, (σ1, g1)) κs (t2, (σ2, g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ns (κs ++ κs') -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗
  NC 1 -∗
  |={⊤,∅}=> |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅, ⊤}=>
  ▷ (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    Φc ∗ state_interp σ2 (length t2') ∗ global_state_interp g2 (n + ns) κs' ∗ C).
Proof.
  iIntros (Hstep) "Hσ Hg He Ht HNC".
  iDestruct (wptp_steps with "Hσ Hg He Ht HNC") as "Hwp"; first done.
  iApply (step_fupdN_wand with "Hwp"); auto.
  iMod 1 as (e2' t2' ?) "(Hσ & Hg & Hwp & Ht & HNC)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    (▷^(S (S (num_laters_per_step (n + ns)))) ⌜ ∀ e2, s = NotStuck → e2 ∈ (e2' :: t2') → not_stuck e2 σ2 g2 ⌝)%I
    (state_interp σ2 (length t2') ∗
    (global_state_interp g2 (n + ns) κs') ∗
     wpc0 s k mj ⊤ e2' Φ Φc ∗ wptp s k t2' ∗ NC 1)%I
    with "[$Hσ $Hg $Hwp $Ht $HNC]") as "(Hsafe&Hσ&Hg&Hwp&Hvs&HNC)".
  { iIntros "(Hσ & Hg & Hwp & Ht & HNC)" (e' -> He').
    apply elem_of_cons in He' as [<-|(t1''&t2''&->)%elem_of_list_split].
    - iPoseProof (wpc_safe with "Hσ Hg Hwp") as "H".
      rewrite ncfupd_eq.
      by iMod ("H" with "[$]") as "($&_)".
    - iDestruct "Ht" as "(_ & He' & _)".
      iPoseProof (wpc_safe with "Hσ Hg He'") as "H".
      rewrite ncfupd_eq.
      by iMod ("H" with "[$]") as "($&_)". }
  iExists _, _. iSplitL ""; first done. iFrame "Hσ Hg".
  iMod (NC_upd_C with "HNC") as "#HC".
  iMod (wpc0_crash with "Hwp") as "H".
  iMod (own_disc_fupd_elim with "H") as "H".
  iSpecialize ("H" with "[$]").
  iMod (fupd_split_level_fupd with "H") as "H".
  iApply fupd_mask_intro_discard; first by set_solver.
  iNext. by iFrame "# ∗".
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
Lemma wptp_strong_adequacy Φ Φc k κs' s n e1 t1 κs t2 σ1 g1 ns σ2 g2 :
  nsteps n (e1 :: t1, (σ1, g1)) κs (t2, (σ2, g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ns (κs ++ κs') -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗
  NC 1 -∗
  |={⊤,∅}=> |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅, ⊤}=> (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ▷^(S (S (num_laters_per_step (n + ns)))) (⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 g2 ⌝) ∗
    state_interp σ2 (length t2') ∗
    global_state_interp g2 (n + ns) κs' ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1).
Proof.
  iIntros (?) "?? Hwpc Hwptp Hnc".
  iApply (wptp0_strong_adequacy 0 with "[$] [$] [Hwpc] [Hwptp] [$]"); first eassumption.
  { by iApply wpc0_wpc. }
  { iApply (big_sepL_mono with "Hwptp"). iIntros.
    iApply (wpc0_wpc); eauto.
  }
Qed.

Lemma wptp_strong_crash_adequacy Φ Φc κs' s k n e1 t1 κs t2 σ1 g1 ns σ2 g2 :
  nsteps n (e1 :: t1, (σ1, g1)) κs (t2, (σ2, g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ns (κs ++ κs') -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗
  NC 1 -∗
  |={⊤,∅}=> |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅, ⊤}=>
  ▷ (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    Φc ∗ state_interp σ2 (length t2') ∗ global_state_interp g2 (n + ns) κs' ∗ C).
Proof.
  iIntros (?) "?? Hwpc Hwptp Hnc".
  iApply (wptp0_strong_crash_adequacy 0 with "[$] [$] [Hwpc] [Hwptp] [$]"); first eassumption.
  { by iApply wpc0_wpc. }
  { iApply (big_sepL_mono with "Hwptp"). iIntros.
    iApply (wpc0_wpc); eauto.
  }
Qed.

End crash_adequacy.
