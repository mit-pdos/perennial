(** Some derived lemmas for ectx-based languages *)
From iris.proofmode Require Import proofmode.
From Perennial.program_logic Require Export ectx_language weakestpre lifting.
From iris.prelude Require Import options.

Section wp.
Context {Λ : ectxLanguage} `{!irisGS Λ Σ, !generationGS Λ Σ}.
Context {Hinh : Inhabited (state Λ)} {Hginh : Inhabited (global_state Λ)}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Local Hint Resolve base_prim_reducible base_reducible_prim_step : core.
Local Definition reducible_not_val_inhabitant e := reducible_not_val e inhabitant.
Local Hint Resolve reducible_not_val_inhabitant : core.
Local Hint Resolve base_stuck_stuck : core.

Lemma wp_lift_base_step_ncfupd {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) -∗ |NC={E,∅}=> ▷
    (⌜base_reducible e1 σ1 g1⌝ ∗
    ∀ e2 σ2 g2 efs, ⌜base_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ -∗ |NC={∅,E}=>
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_ncfupd=>//. iIntros (σ1 g1 ns mj D κ κs nt) "Hσ Hg".
  iMod ("H" with "Hσ Hg") as "H". iModIntro.
  iNext. iDestruct "H" as "[% H]".
  iSplit; first by destruct s; eauto. iIntros (e2 σ2 g2 efs ?).
  iIntros "Hlc".
  iApply "H"; eauto.
Qed.

Lemma wp_lift_base_step_fupd {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) ={E,∅}=∗ ▷
    (⌜base_reducible e1 σ1 g1⌝ ∗
    ∀ e2 σ2 g2 efs, ⌜base_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ ={∅,E}=∗
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd=>//. iIntros (σ1 g1 ns mj D κ κs nt) "Hσ Hg".
  iMod ("H" with "Hσ Hg") as "H". iModIntro.
  iNext. iDestruct "H" as "[% H]".
  iSplit; first by destruct s; eauto. iIntros (e2 σ2 g2 efs ?).
  iIntros "Hlc".
  iApply "H"; eauto.
Qed.

Lemma wp_lift_base_step_nc {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) -∗ |NC={E,∅}=>
    ⌜base_reducible e1 σ1 g1⌝ ∗
    ▷ ∀ e2 σ2 g2 efs, ⌜base_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ -∗ |NC={∅,E}=>
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_base_step_ncfupd; [done|]. iIntros (????????) "??".
  iMod ("H" with "[$] [$]") as "[$ H]". iIntros "!> !>" (e2 σ2 g2 efs ?). by iApply "H".
Qed.

Lemma wp_lift_base_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) ={E,∅}=∗
    ⌜base_reducible e1 σ1 g1⌝ ∗
    ▷ ∀ e2 σ2 g2 efs, ⌜base_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ ={∅,E}=∗
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_base_step_fupd; [done|]. iIntros (????????) "??".
  iMod ("H" with "[$] [$]") as "[$ H]". iIntros "!> !>" (e2 σ2 g2 efs ?). by iApply "H".
Qed.

(*
Lemma wp_lift_base_stuck E Φ e :
  to_val e = None →
  sub_redexes_are_values e →
  (∀ σ ns κs nt, state_interp σ ns κs nt ={E,∅}=∗ ⌜base_stuck e σ⌝)
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (??) "H". iApply wp_lift_stuck; first done.
  iIntros (σ ns κs nt) "Hσ". iMod ("H" with "Hσ") as "%". by auto.
Qed.

Lemma wp_lift_pure_base_stuck E Φ e :
  to_val e = None →
  sub_redexes_are_values e →
  (∀ σ, base_stuck e σ) →
  ⊢ WP e @ E ?{{ Φ }}.
Proof using Hinh.
  iIntros (?? Hstuck). iApply wp_lift_base_stuck; [done|done|].
  iIntros (σ ns κs nt) "_". iApply fupd_mask_intro; by auto with set_solver.
Qed.
*)

(*
Lemma wp_lift_atomic_base_step_fupd {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E1}=∗
    ⌜base_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜base_step e1 σ1 κ e2 σ2 efs⌝ ={E1}[E2]▷=∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (σ1 ns κ κs nt) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by destruct s; auto. iIntros (e2 σ2 efs Hstep).
  iApply "H"; eauto.
Qed.
*)

Lemma wp_lift_atomic_base_step_nc {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) -∗ |NC={E}=>
    ⌜base_reducible e1 σ1 g1⌝ ∗
    ▷ ∀ e2 σ2 g2 efs, ⌜base_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ -∗ |NC={E}=>
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_nc; eauto.
  iIntros (σ1 g1 ns mj D κ κs nt) "Hσ1 Hg1". iMod ("H" with "Hσ1 Hg1") as "[% H]"; iModIntro.
  iSplit; first by destruct s; auto. iNext. iIntros (e2 σ2 g2 efs Hstep).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_base_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) ={E}=∗
    ⌜base_reducible e1 σ1 g1⌝ ∗
    ▷ ∀ e2 σ2 g2 efs, ⌜base_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ ={E}=∗
      state_interp σ2 (length efs + nt) ∗
      global_state_interp g2 (step_count_next ns) mj D κs ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (σ1 g1 ns mj D κ κs nt) "Hσ1 Hg1". iMod ("H" with "Hσ1 Hg1") as "[% H]"; iModIntro.
  iSplit; first by destruct s; auto. iNext. iIntros (e2 σ2 g2 efs Hstep).
  iIntros "Hlc".
  iApply "H"; eauto.
Qed.

(*
Lemma wp_lift_atomic_base_step_no_fork_fupd {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E1}=∗
    ⌜base_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜base_step e1 σ1 κ e2 σ2 efs⌝ ={E1}[E2]▷=∗
      ⌜efs = []⌝ ∗ state_interp σ2 (S ns) κs nt ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_base_step_fupd; [done|].
  iIntros (σ1 ns κ κs nt) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iIntros (v2 σ2 efs Hstep).
  iMod ("H" $! v2 σ2 efs with "[# //]") as "H".
  iIntros "!> !>". iMod "H" as "(-> & ? & ?) /=". by iFrame.
Qed.
*)

Lemma wp_lift_atomic_base_step_no_fork_nc {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) -∗ |NC={E}=>
    ⌜base_reducible e1 σ1 g1⌝ ∗
    ▷ ∀ e2 σ2 g2 efs, ⌜base_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ -∗ |NC={E}=>
      ⌜efs = []⌝ ∗ state_interp σ2 nt ∗ global_state_interp g2 (step_count_next ns) mj D κs ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_base_step_nc; eauto.
  iIntros (σ1 g1 ns mj D κ κs nt) "Hσ1 Hg1". iMod ("H" $! σ1 with "Hσ1 Hg1") as "[$ H]"; iModIntro.
  iNext; iIntros (v2 σ2 g2 efs Hstep).
  iMod ("H" $! v2 σ2 g2 efs with "[//]") as "(-> & ? & ? & ?) /=". by iFrame.
Qed.

Lemma wp_lift_atomic_base_step_no_fork {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 g1 ns mj D κ κs nt, state_interp σ1 nt -∗ global_state_interp g1 ns mj D (κ ++ κs) ={E}=∗
    ⌜base_reducible e1 σ1 g1⌝ ∗
    ▷ ∀ e2 σ2 g2 efs, ⌜base_step e1 σ1 g1 κ e2 σ2 g2 efs⌝ ={E}=∗
      ⌜efs = []⌝ ∗ state_interp σ2 nt ∗ global_state_interp g2 (step_count_next ns) mj D κs ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_base_step; eauto.
  iIntros (σ1 g1 ns mj D κ κs nt) "Hσ1 Hg1". iMod ("H" $! σ1 with "Hσ1 Hg1") as "[$ H]"; iModIntro.
  iNext; iIntros (v2 σ2 g2 efs Hstep).
  iMod ("H" $! v2 σ2 g2 efs with "[//]") as "(-> & ? & ? & ?) /=". by iFrame.
Qed.

Lemma wp_lift_pure_det_base_step_no_fork {s E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1 g1, base_reducible e1 σ1 g1) →
  (∀ σ1 g1 κ e2' σ2 g2 efs',
    base_step e1 σ1 g1 κ e2' σ2 g2 efs' → κ = [] ∧ σ2 = σ1 ∧ g2 = g1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E}[E']▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh Hginh.
  intros. rewrite -(wp_lift_pure_det_step_no_fork e1 e2); eauto.
  { iIntros "H". iApply (step_fupd_wand with "H"). by iIntros. }
  destruct s; by auto.
Qed.

Lemma wp_lift_pure_det_base_step_no_fork' {s E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1 g1, base_reducible e1 σ1 g1) →
  (∀ σ1 g1 κ e2' σ2 g2 efs',
    base_step e1 σ1 g1 κ e2' σ2 g2 efs' → κ = [] ∧ σ2 = σ1 ∧ g2 = g1 ∧ e2' = e2 ∧ efs' = []) →
  ▷ WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh Hginh.
  intros. rewrite -[(WP e1 @ s; _ {{ _ }})%I]wp_lift_pure_det_base_step_no_fork //.
  rewrite -step_fupd_intro //.
Qed.
End wp.
