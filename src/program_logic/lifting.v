(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export weakestpre.
From iris.prelude Require Import options.

Section lifting.
Context `{!irisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Local Hint Resolve reducible_no_obs_reducible : core.

Lemma wp_lift_step_fupdN s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) ={E,∅}=∗
    |={∅}▷=>^(S $ num_laters_per_step ns)
    ⌜if s is NotStuck then reducible e1 σ1 g1 else True⌝ ∗
    ∀ e2 σ2 g2 efs, ⌜prim_step e1 σ1 g1 κ e2 σ2 g2 efs⌝
       ={∅,E}=∗
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  rewrite wp_eq /wp_def !wpc_unfold /wpc_pre=>->.
  iIntros "H" (mj). iSplit; last first.
  { iIntros. iApply step_fupd_extra.step_fupd2N_inner_later; auto. iNext; iFrame. }
  iIntros (????????) "Hσ Hg HNC".
  iSpecialize ("H" with "[$] [$]").
  iMod "H".
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; try set_solver+.
  iModIntro. iApply step_fupd_extra.step_fupdN_step_fupd2N.
  iApply (step_fupdN_wand with "H"). iIntros "($&H)".
  iIntros. iMod "Hclo". iMod ("H" with "[//]") as "($ & $ & He & Hef)".
  iModIntro. iFrame. iSplitL "He".
  - iApply wpc0_wpc.
    iApply (wpc_strong_mono' with "[$]"); auto.
    destruct (to_val); set_solver.
  - iApply (big_sepL_mono with "Hef")=>???/=. iApply wpc0_wpc.
Qed.

Lemma wp_lift_step_fupd s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) ={E,∅}=∗ ▷
    (⌜if s is NotStuck then reducible e1 σ1 g1 else True⌝ ∗
    ∀ e2 σ2 g2 efs, ⌜prim_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ ={∅,E}=∗
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  intros ?. rewrite -wp_lift_step_fupdN; [|done]. simpl.
  iIntros "H". iIntros (????????) "Hσ Hg".
  iMod ("H" with "[$] [$]") as "(Hr&N)".
  iModIntro.
  iApply step_fupdN_intro; first done.
  iModIntro. iNext. iModIntro. iNext. eauto.
Qed.

(*
Lemma wp_lift_stuck E Φ e :
  to_val e = None →
  (∀ σ ns κs nt, state_interp σ ns κs nt ={E,∅}=∗ ⌜stuck e σ⌝)
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre=>->. iIntros "H" (q σ1 ns κ κs nt) "Hσ HNC".
  iMod ("H" with "Hσ") as %[? Hirr]. iModIntro. iSplit; first done.
  iIntros (e2 σ2 efs ?). by case: (Hirr κ e2 σ2 efs).
Qed.
*)

(** Derived lifting lemmas. *)
Lemma wp_lift_step s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 g1 else True⌝ ∗
    ▷ ∀ e2 σ2 g2 efs, ⌜prim_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ ={∅,E}=∗
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (????????) "Hσ Hg".
  iMod ("H" with "Hσ Hg") as "[$ H]". iModIntro. iNext. iIntros "* %". by iApply "H".
Qed.

Lemma wp_lift_pure_step_no_fork `{!Inhabited (state Λ), !Inhabited (global_state Λ)} s E E' Φ e1 :
  (∀ σ1 g1, if s is NotStuck then reducible e1 σ1 g1 else to_val e1 = None) →
  (∀ κ σ1 g1 e2 σ2 g2 efs, prim_step e1 σ1 g1 κ e2 σ2 g2 efs → κ = [] ∧ σ2 = σ1 ∧ g2 = g1 ∧ efs = []) →
  (|={E}[E']▷=> ∀ κ e2 efs σ g, ⌜prim_step e1 σ g κ e2 σ g efs⌝ → WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant inhabitant). destruct s; eauto using reducible_not_val. }
  iIntros (σ1 g1 ns mj D κ κs nt) "Hσ Hg". iMod "H".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. destruct s; done. }
  iNext. iIntros (e2 σ2 g2 efs ?).
  destruct (Hstep κ σ1 g1 e2 σ2 g2 efs) as (-> & <- & <- & ->); auto.
  iFrame "Hσ". iMod (global_state_interp_le with "Hg") as "$".
  { apply step_count_next_incr. }
  iMod "Hclose" as "_". iMod "H". iModIntro.
  by iDestruct ("H" with "[//]") as "$".
Qed.

(*
Lemma wp_lift_pure_stuck `{!Inhabited (state Λ)} E Φ e :
  (∀ σ, stuck e σ) →
  True ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (Hstuck) "_". iApply wp_lift_stuck.
  - destruct(to_val e) as [v|] eqn:He; last done.
    rewrite -He. by case: (Hstuck inhabitant).
  - iIntros (σ ns κs nt) "_". iApply fupd_mask_intro; auto with set_solver.
Qed.
*)

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. *)
(*
Lemma wp_lift_atomic_step_fupd {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E1}[E2]▷=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={E1}=∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s E1 _ e1)=>//; iIntros (σ1 ns κ κs nt) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "H".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose". iNext.

iMod "Hclose" as "_".
  iIntros "Hclose" (e2 σ2 efs ?). iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs with "[#]") as "H"; [done|].
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
  iMod "Hclose" as "_". iMod "H" as "($ & HQ & $)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply wp_value; last done. by apply of_to_val.
Qed.
*)

Lemma wp_lift_atomic_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) ={E}=∗
    ⌜if s is NotStuck then reducible e1 σ1 g1 else True⌝ ∗
    ▷ ∀ e2 σ2 g2 efs, ⌜prim_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ ={E}=∗
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s E _ e1)=>//; iIntros (σ1 g1 ns mj D κ κs nt) "Hσ1 Hg1".
  iMod ("H" with "[$] [$]") as "[$ H]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose". iNext.
  iIntros. iMod "Hclose". iMod ("H" with "[//]") as "($ & $ & H & ?)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iFrame. iModIntro. iApply wp_value; last done. by apply of_to_val.
Qed.

Lemma wp_lift_pure_det_step_no_fork `{!Inhabited (state Λ), !Inhabited (global_state Λ)} {s E E' Φ} e1 e2 :
  (∀ σ1 g1, if s is NotStuck then reducible e1 σ1 g1 else to_val e1 = None) →
  (∀ σ1 g1 κ e2' σ2 g2 efs', prim_step e1 σ1 g1 κ e2' σ2 g2 efs' →
    κ = [] ∧ σ2 = σ1 ∧ g2 = g1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E}[E']▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step_no_fork s E E'); try done.
  { naive_solver. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (κ e' efs' σ g (_&?&?&->&?)%Hpuredet); auto.
Qed.

Lemma wp_pure_step_fupd `{!Inhabited (state Λ), !Inhabited (global_state Λ)} s E E' e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  (|={E}[E']▷=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply wp_lift_pure_det_step_no_fork.
  - intros σ g. specialize (Hsafe σ g). destruct s; eauto using reducible_not_val.
  - done.
  - by iApply (step_fupd_wand with "Hwp").
Qed.

Lemma wp_pure_step_later `{!Inhabited (state Λ), !Inhabited (global_state Λ)} s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  ▷^n WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.
End lifting.
