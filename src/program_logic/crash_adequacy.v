From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export step_fupd_extra crash_lang crash_weakestpre.
Import uPred.
Import language.

Set Default Proof Using "Type".

Section crash_adequacy.
Context `{!irisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Context (mj: fracR).
(* The IH of the theorems here requires working with some fixed choice of mj in the wpc0 form,
   instead of wpc. So, we introduce here a notation to insert the mj explicitly to porting these proofs easier *)
Local Notation "'WPC' e @ k ; E1 {{ Φ } } {{ Φc } }" := (wpc0 NotStuck k%nat mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Local Notation "'WPC' e @ s ; k ; E1 {{ Φ } } {{ Φc } }" := (wpc0 s k%nat mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Local Notation "'WPC' e @ s ; k ; E1 {{ Φ } } {{ Φc } }" := (wpc0 s k%nat mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : stdpp_scope.

Notation wptp s k t := ([∗ list] ef ∈ t, WPC ef @ s; k; ⊤ {{ fork_post }} {{ True }})%I.

Lemma wpc_step s k e1 σ1 g1 ns D κ κs e2 σ2 g2 efs m Φ Φc :
  prim_step e1 σ1 g1 κ e2 σ2 g2 efs →
  state_interp σ1 m -∗
  global_state_interp g1 ns mj D (κ ++ κs) -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗ NC 1 -∗
  ||={⊤|⊤,∅|∅}=> ||▷=>^(S $ num_laters_per_step ns) ||={∅|∅,⊤|⊤}=>
  state_interp σ2 (length efs + m) ∗
  global_state_interp g2 (step_count_next ns) mj D κs ∗
  WPC e2 @ s; k; ⊤ {{ Φ }} {{ Φc }} ∗
  wptp s k efs ∗
  NC 1.
Proof.
  rewrite {1}wpc0_unfold /wpc_pre. iIntros (?) "Hσ Hg H HNC".
  rewrite (val_stuck e1 σ1 g1 κ e2 σ2 g2 efs) //.
  iDestruct "H" as "(H&_)".
  iMod (fupd2_mask_subseteq ⊤ (⊤ ∖ D)) as "Hclo"; try set_solver+.
  iMod ("H" $! _ σ1 with "Hσ Hg HNC") as "H".
  iModIntro.
  iApply (step_fupd2N_wand with "H"). iIntros "(_&H)".
  iMod ("H" $! e2 σ2 g2 efs with "[//]") as "H".
  iMod "Hclo". iModIntro. eauto.
  destruct (to_val e2); eauto.
Qed.

Lemma wptp_step s k e1 t1 t2 κ κs σ1 g1 ns D σ2 g2 Φ Φc :
  step (e1 :: t1,(σ1,g1)) κ (t2, (σ2,g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ns mj D (κ ++ κs) -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }}-∗ wptp s k t1 -∗ NC 1 ==∗
  ∃ e2 t2', ⌜t2 = e2 :: t2'⌝ ∗
  ||={⊤|⊤,∅|∅}=> ||▷=>^(S $ num_laters_per_step ns) ||={∅|∅,⊤|⊤}=>
  state_interp σ2 (pred (length t2)) ∗
  global_state_interp g2 (step_count_next ns) mj D κs ∗
  WPC e2 @ s; k; ⊤ {{ Φ }} {{ Φc}} ∗ wptp s k t2' ∗ NC 1.
Proof.
  iIntros (Hstep) "Hσ Hg He Ht HNC".
  destruct Hstep as [e1' σ1' g1' e2' σ2' g2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', (t2' ++ efs). iModIntro. iSplitR; first by eauto.
    iMod (wpc_step with "Hσ Hg He HNC") as "H"; first done. iModIntro.
    iApply (step_fupd2N_wand with "H"). iIntros ">(Hσ & Hg & He2 & Hefs) !>".
    rewrite Nat.add_comm app_length. by iFrame.
  - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
    iDestruct "Ht" as "(Ht1 & He1 & Ht2)".
    iModIntro. iMod (wpc_step with "Hσ Hg He1 HNC") as "H"; first done. iModIntro.
    iApply (step_fupd2N_wand with "H"). iIntros ">(Hσ & Hg & He2 & Hefs) !>".
    rewrite !app_length /= !app_length.
    replace (length t1' + S (length t2' + length efs))
      with (length efs + (length t1' + S (length t2'))) by lia. by iFrame.
Qed.
(* The total number of laters used between the physical steps number
   [start] (included) to [start+ns] (excluded). *)
Local Fixpoint steps_sum (num_laters_per_step step_count_next : nat → nat) (start ns : nat) : nat :=
  match ns with
  | O => 0
  | S ns =>
    S $ num_laters_per_step start + steps_sum num_laters_per_step step_count_next (step_count_next start) ns
  end.

Lemma steps_sum_S (num_laters_per_step step_count_next : nat → nat) (start ns : nat) :
  steps_sum num_laters_per_step step_count_next start (S ns) =
  steps_sum num_laters_per_step step_count_next (step_count_next start) ns + S (num_laters_per_step start).
Proof. induction ns => //=; try lia. Qed.

Lemma steps_sum_S_r (num_laters_per_step step_count_next : nat → nat) (start ns : nat) :
  steps_sum num_laters_per_step step_count_next start (S ns) =
  steps_sum num_laters_per_step step_count_next start ns + S (num_laters_per_step (Nat.iter ns step_count_next start)).
Proof.
  revert start.
  induction ns => start.
  - rewrite //=; lia.
  - rewrite steps_sum_S IHns. simpl.
    rewrite -Nat_iter_S_r /=. lia.
Qed.

Lemma wptp_steps s k n e1 t1 κs κs' t2 σ1 g1 ns D σ2 g2 Φ Φc :
  nsteps n (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ns mj D (κs ++ κs') -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗ wptp s k t1 -∗ NC 1 -∗
  (||={⊤|⊤, ∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ns n) ||={∅|∅,⊤|⊤}=> ∃ e2 t2',
    ⌜t2 = e2 :: t2'⌝ ∗
    state_interp σ2 (pred (length t2)) ∗
    global_state_interp g2 (Nat.iter n step_count_next ns) mj D κs' ∗
    WPC e2 @ s; k; ⊤ {{ Φ }} {{ Φc }} ∗ wptp s k t2' ∗
    NC 1).
Proof.
  revert e1 t1 κs κs' t2 σ1 g1 ns σ2 g2; simpl.
  induction n as [|n IH]=> e1 t1 κs κs' t2 σ1 g1 ns σ2 g2 /=.
  { inversion_clear 1; iIntros "?????"; iExists e1, t1; iFrame; eauto 10.
    iApply fupd2_mask_intro_subseteq; eauto. }
  iIntros (Hsteps) "Hσ Hg He Ht HNC". inversion_clear Hsteps as [|?? [t1' [σ1' g1']]].
  rewrite -(assoc_L (++)).
  iApply step_fupd2N_inner_plus.
  iMod (wptp_step with "Hσ Hg He Ht HNC") as (e1' t1'' ?) ">H"; first eauto; simplify_eq.
  iApply (step_fupd2N_wand with "H"). iIntros "!> H".
  iMod "H".
  iDestruct "H" as "(Hσ & Hg & He & Ht & HNC)".
  iMod (IH with "Hσ Hg He Ht HNC") as "IH"; first done.
  rewrite -Nat_iter_S_r.
  iModIntro. iModIntro. eauto.
Qed.

Lemma wpc_safe k κs m e σ g ns D Φ Φc q :
  state_interp σ m -∗
  global_state_interp g ns mj D κs -∗
  WPC e @ k ; ⊤  {{ Φ }} {{ Φc }} -∗ NC q -∗ ||={⊤|⊤, ⊤|⊤}=>
  ▷^(S (S (num_laters_per_step ns))) ⌜is_Some (to_val e) ∨ reducible e σ g⌝.
Proof.
  rewrite wpc0_unfold /wpc_pre. iIntros "Hσ Hg H". iDestruct "H" as "(H&_)".
  destruct (to_val e) as [v|] eqn:?; first by eauto.
  iIntros "HNC".
  iApply (step_fupd2N_inner_plain' (S (num_laters_per_step ns))).
  iMod (fupd2_mask_subseteq ⊤ (⊤ ∖ D)) as "Hclo"; try set_solver+.
  iMod ("H" $! _ _ _ _ _ [] with "[$] [$] [$]") as "H".
  simpl. iModIntro. iApply (step_fupd2N_wand with "H").
  iNext. iIntros "(%Hred&Hclo')". eauto.
Qed.

Lemma wptp0_strong_adequacy Φ Φc k κs' s n e1 t1 κs t2 σ1 g1 ns D σ2 g2 :
  nsteps n (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ns mj D (κs ++ κs') -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗
  NC 1 -∗
  ||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ns n) ||={∅|∅, ⊤|⊤}=> (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ▷^(S (S (num_laters_per_step ((Nat.iter n step_count_next ns))))) (⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 g2 ⌝) ∗
    state_interp σ2 (length t2') ∗
    global_state_interp g2 (Nat.iter n step_count_next ns) mj D κs' ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1).
Proof.
  iIntros (Hstep) "Hσ Hg He Ht HNC".
  iMod (wptp_steps with "Hσ Hg He Ht HNC") as "Hwp"; first done.
  iModIntro. iApply (step_fupd2N_wand with "Hwp").
  iMod 1 as (e2' t2' ?) "(Hσ & Hg & Hwp & Ht & HNC)"; simplify_eq/=.
  iMod (fupd2_plain_keep_l ⊤ ⊤
    (▷^(S (S (num_laters_per_step ((Nat.iter n step_count_next ns))))) ⌜ ∀ e2, s = NotStuck → e2 ∈ (e2' :: t2') → not_stuck e2 σ2 g2 ⌝)%I
    (state_interp σ2 (length t2') ∗
    (global_state_interp g2 (Nat.iter n step_count_next ns) mj D κs') ∗
     wpc0 s k mj ⊤ e2' Φ Φc ∗ wptp s k t2' ∗ NC 1)%I
    with "[$Hσ $Hg $Hwp $Ht $HNC]") as "(Hsafe&Hσ&Hg&Hwp&Hvs&HNC)".
  { iIntros "(Hσ & Hg & Hwp & Ht & HNC)". iIntros (e' -> He').
    apply elem_of_cons in He' as [<-|(t1''&t2''&->)%elem_of_list_split].
    - iPoseProof (wpc_safe with "Hσ Hg Hwp") as "H".
      iMod ("H" with "[$]") as "H"; eauto.
    - iDestruct "Ht" as "(_ & He' & _)".
      iPoseProof (wpc_safe with "Hσ Hg He'") as "H".
      by iMod ("H" with "[$]") as "H". }
  iExists _, _. iSplitL ""; first done. iFrame "Hsafe Hσ".
  iMod (fupd2_mask_subseteq ⊤ (⊤ ∖ D)) as "Hclo"; try set_solver+.
  iMod (wpc0_value_inv_option with "Hwp Hg HNC") as "($&Hg&HNC)".
  clear Hstep. iMod "Hclo" as "_". iInduction t2' as [|e t2'] "IH"; csimpl; first by iFrame.
  iDestruct "Hvs" as "[Hv Hvs]". destruct (to_val e) as [v|] eqn:He.
  + apply of_to_val in He as <-.
    iMod (fupd2_mask_subseteq ⊤ (⊤ ∖ D)) as "Hclo'"; try set_solver+.
    iMod (wpc0_value_inv' with "Hv Hg HNC") as "($&?&?)".
    iMod "Hclo'" as "_".
    by iApply ("IH" with "[$] [$] [$]").
  + by iApply ("IH" with "[$] [$]").
Qed.

Lemma wptp0_strong_crash_adequacy Φ Φc κs' s k n e1 t1 κs t2 σ1 g1 ns D σ2 g2 :
  nsteps n (e1 :: t1, (σ1, g1)) κs (t2, (σ2, g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ns mj D (κs ++ κs') -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗
  NC 1 -∗
  ||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ns (S n)) ||={∅|∅, ⊤|⊤}=>
  ▷ (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    Φc ∗ state_interp σ2 (length t2') ∗ global_state_interp g2 ((Nat.iter n step_count_next ns)) mj D κs' ∗ C).
Proof.
  iIntros (Hstep) "Hσ Hg He Ht HNC".
  iDestruct (wptp_steps with "Hσ Hg He Ht HNC") as "Hwp"; first done.
  rewrite steps_sum_S_r.
  iApply step_fupd2N_inner_plus.
  iApply (step_fupd2N_inner_wand with "Hwp"); auto.
  iDestruct 1 as (e2' t2' ?) "(Hσ & Hg & Hwp & Ht & HNC)"; simplify_eq/=.
  iMod (fupd2_plain_keep_l ⊤ ⊤
    (▷^(S (S (num_laters_per_step ((Nat.iter n step_count_next ns)))))
         ⌜ ∀ e2, s = NotStuck → e2 ∈ (e2' :: t2') → not_stuck e2 σ2 g2 ⌝)%I
    (state_interp σ2 (length t2') ∗
    (global_state_interp g2 ((Nat.iter n step_count_next ns)) mj D κs') ∗
     wpc0 s k mj ⊤ e2' Φ Φc ∗ wptp s k t2' ∗ NC 1)%I
    with "[$Hσ $Hg $Hwp $Ht $HNC]") as "(Hsafe&Hσ&Hg&Hwp&Hvs&HNC)".
  { iIntros "(Hσ & Hg & Hwp & Ht & HNC)" (e' -> He').
    apply elem_of_cons in He' as [<-|(t1''&t2''&->)%elem_of_list_split].
    - iPoseProof (wpc_safe with "Hσ Hg Hwp") as "H".
      iMod ("H" with "[$]") as "H". iModIntro. eauto.
    - iDestruct "Ht" as "(_ & He' & _)".
      iPoseProof (wpc_safe with "Hσ Hg He'") as "H".
      iMod ("H" with "[$]") as "H". eauto. }
  iMod (fupd2_mask_subseteq ⊤ (⊤ ∖ D)) as "Hclo"; try set_solver+.
  iMod (NC_upd_C with "HNC") as "#HC".
  iPoseProof (wpc0_crash with "[$] Hg [$]") as "H".
  iMod "Hclo".
  iApply (step_fupd2N_inner_wand _ _ _ _ (S _) with "H"); auto.
  iIntros "(Hg&HΦc)". iNext. iExists _, _. iSplitL ""; first done.
  iFrame. eauto.
Qed.
End crash_adequacy.

Section crash_adequacy.
Context `{!irisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

(* Now we prove a version where we use normal wpc instead of wpc0. *)

Notation wptp s k t := ([∗ list] ef ∈ t, WPC ef @ s; k; ⊤ {{ fork_post }} {{ True }})%I.

Lemma wptp_strong_adequacy Φ Φc k κs' s n e1 t1 κs t2 σ1 g1 ns mj D σ2 g2 :
  nsteps n (e1 :: t1, (σ1, g1)) κs (t2, (σ2, g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ns mj D (κs ++ κs') -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗
  NC 1 -∗
  ||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ns n) ||={∅|∅, ⊤|⊤}=> (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ▷^(S (S (num_laters_per_step (Nat.iter n step_count_next ns)))) (⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 g2 ⌝) ∗
    state_interp σ2 (length t2') ∗
    global_state_interp g2 ((Nat.iter n step_count_next ns)) mj D κs' ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1).
Proof.
  iIntros (?) "?? Hwpc Hwptp Hnc".
  iApply (wptp0_strong_adequacy mj with "[$] [$] [Hwpc] [Hwptp] [$]"); first eassumption.
  { by iApply wpc0_wpc. }
  { iApply (big_sepL_mono with "Hwptp"). iIntros.
    iApply (wpc0_wpc); eauto.
  }
Qed.

Lemma wptp_strong_crash_adequacy Φ Φc κs' s k n e1 t1 κs t2 σ1 g1 ns mj D σ2 g2 :
  nsteps n (e1 :: t1, (σ1, g1)) κs (t2, (σ2, g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ns mj D (κs ++ κs') -∗
  WPC e1 @ s; k; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗
  NC 1 -∗
  ||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ns (S n)) ||={∅|∅, ⊤|⊤}=>
  ▷ (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    Φc ∗ state_interp σ2 (length t2') ∗ global_state_interp g2 (Nat.iter n step_count_next ns) mj D κs' ∗ C).
Proof.
  iIntros (?) "?? Hwpc Hwptp Hnc".
  iApply (wptp0_strong_crash_adequacy mj with "[$] [$] [Hwpc] [Hwptp] [$]"); first eassumption.
  { by iApply wpc0_wpc. }
  { iApply (big_sepL_mono with "Hwptp"). iIntros.
    iApply (wpc0_wpc); eauto.
  }
Qed.

End crash_adequacy.
