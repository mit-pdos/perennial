Require Export Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Abstraction.
Require Export Spec.Layer.
Require Export WeakestPre.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section lifting.
  Context {OpT: Type → Type}.
  Context `{Λ: Layer OpT}.
  Context `{irisG OpT Λ Σ}.
Implicit Types s : stuckness.
Implicit Types σ : State Λ.
Implicit Types P Q : iProp Σ.

Lemma wp_lift_step_fupd {T} s E Φ (e1: proc OpT T) :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜if s is NotStuck then non_errorable e1 σ1 else True⌝ ∗
    ∀ e2 σ2 (efs: thread_pool OpT), ⌜exec_step (Λ.(sem)) e1 σ1 (Val σ2 (e2, efs))⌝ ={∅,∅,E}▷=∗
                 state_interp σ2 ∗ WP e2 @ s; E {{ Φ }} ∗
                 [∗ list] ef ∈ efs, WP (projT2 ef) @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre=>->. iIntros "H" (σ1) "Hσ".
  iMod ("H" with "Hσ") as "(%&H)". iModIntro. iSplit. by destruct s. done.
Qed.

(** Derived lifting lemmas. *)
Lemma wp_lift_step {T} s E Φ (e1 : proc OpT T) :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜if s is NotStuck then non_errorable e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜exec_step (Λ.(sem)) e1 σ1 (Val σ2 (e2, efs)) ⌝ ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP (projT2 ef) @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (?) "Hσ".
  iMod ("H" with "Hσ") as "[$ H]". iIntros "!> * % !>". by iApply "H".
Qed.

Lemma wp_lift_pure_step {T} `{Inhabited (State Λ)} s E E' Φ (e1: proc OpT T) :
  (∀ σ1, if s is NotStuck then non_errorable e1 σ1 ∧ to_val e1 = None else to_val e1 = None) →
  (∀ σ1 e2 σ2 efs, exec_step (Λ.(sem)) e1 σ1 (Val σ2 (e2, efs)) → σ1 = σ2) →
  (|={E,E'}▷=> ∀ e2 efs σ, ⌜exec_step (Λ.(sem)) e1 σ (Val σ (e2, efs))⌝ →
    WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP (projT2 ef) @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant). destruct s; intuition. }
  iIntros (σ1) "Hσ". iMod "H".
  iMod fupd_intro_mask' as "Hclose"; last iModIntro; first by set_solver. iSplit.
  { iPureIntro. destruct s; intuition; eapply Hsafe. }
  iNext. iIntros (e2 σ2 efs ?).
  destruct (Hstep σ1 e2 σ2 efs); auto; subst.
  iMod "Hclose" as "_". iFrame "Hσ". iMod "H". iApply "H"; auto.
Qed.

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. *)
Lemma wp_lift_atomic_step_fupd {T} {s E1 E2 Φ} (e1: proc OpT T) :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜if s is NotStuck then non_errorable e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜exec_step (Λ.(sem)) e1 σ1 (Val σ2 (e2, efs))⌝ ={E1,E2}▷=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2) ∗ [∗ list] ef ∈ efs, WP (projT2 ef) @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply (wp_lift_step_fupd s E1 _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iMod (fupd_intro_mask' E1 ∅) as "Hclose"; first set_solver.
  iIntros "!>" (e2 σ2 efs ?). iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs with "[#]") as "H"; [done|].
  iMod (fupd_intro_mask' E2 ∅) as "Hclose"; [set_solver|]. iIntros "!> !>".
  iMod "Hclose" as "_". iMod "H" as "($ & HΦ & $)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply wp_value; last done. by apply of_to_val.
Qed.

Lemma wp_lift_atomic_step {T} {s E Φ} (e1: proc OpT T):
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜if s is NotStuck then non_errorable e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜exec_step (Λ.(sem)) e1 σ1 (Val σ2 (e2, efs))⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2) ∗ [∗ list] ef ∈ efs, WP (projT2 ef) @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (?) "?". iMod ("H" with "[$]") as "[$ H]". iIntros "!> * % !> !>".
  by iApply "H".
Qed.

Lemma wp_lift_pure_det_step {T} `{Inhabited (State Λ)} {s E E' Φ} (e1: proc OpT T) e2 efs :
  (∀ σ1, if s is NotStuck then non_errorable e1 σ1 ∧ to_val e1 = None else to_val e1 = None) →
  (∀ σ1 e2' σ2 efs', exec_step (Λ.(sem)) e1 σ1 (Val σ2 (e2', efs'))
                     → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs')→
  (|={E,E'}▷=> WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP (projT2 ef) @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step s E E'); try done.
  { by intros; eapply Hpuredet. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  by iIntros (e' efs' σ (_&->&->)%Hpuredet).
Qed.

(*
Lemma wp_pure_step_fupd `{Inhabited (State Λ)} s E E' e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  Nat.iter n (λ P, |={E,E'}▷=> P) (WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply wp_lift_pure_det_step.
  - intros σ. specialize (Hsafe σ). destruct s; eauto using reducible_not_val.
  - destruct s; naive_solver.
  - rewrite /= right_id. by iApply (step_fupd_wand with "Hwp").
Qed.

Lemma wp_pure_step_later `{Inhabited (state Λ)} s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  ▷^n WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.
*)
End lifting.