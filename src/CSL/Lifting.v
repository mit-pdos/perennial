From Transitions Require Import Relations Rewriting.

Require Export Spec.Proc.
Require Import Spec.ProcTheorems.
Require Export Spec.Layer.
Require Export CSL.WeakestPre.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Global Unset Implicit Arguments.

Section lifting.
  Context {OpT: Type → Type}.
  Context `{Λ: Layer OpT}.
  Context `{irisG OpT Λ Σ}.
Implicit Types s : stuckness.
Implicit Types σ : State Λ.
Implicit Types P Q : iProp Σ.

Lemma wp_lift_pre_step {T} s E Φ (e1: proc OpT T) :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,E}=∗ state_interp σ1 ∗ WP e1 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  rewrite {2}wp_unfold /wp_pre=> Heq. rewrite Heq.
  iIntros "Hwand".
  iIntros (σ) "H".
  iMod ("Hwand" with "H") as "(Hinterp&Hwp)".
  rewrite wp_unfold /wp_pre. rewrite Heq.
  by iApply "Hwp".
Qed.

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

Lemma wp_lift_pure_step {T} s E E' Φ (e1: proc OpT T) :
  (if s is NotStuck then (∀ σ1, non_errorable e1 σ1) ∧ to_val e1 = None else to_val e1 = None) →
  (∀ σ1 e2 σ2 efs, exec_step (Λ.(sem)) e1 σ1 (Val σ2 (e2, efs)) → σ1 = σ2) →
  (|={E,E'}▷=> ∀ e2 efs σ, ⌜exec_step (Λ.(sem)) e1 σ (Val σ (e2, efs))⌝ →
    WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP (projT2 ef) @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { destruct s; intuition. }
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

Lemma wp_lift_call_step {T} {s E Φ} (op: OpT T):
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜if s is NotStuck then ¬ snd_lift ( Λ.(sem).(step) op) σ1 Err else True⌝ ∗
    ▷ ∀ e2 σ2, ⌜snd_lift (Λ.(sem).(step) op) σ1 (Val σ2 e2)⌝ ={E}=∗
      state_interp σ2 ∗ Φ e2)
  ⊢ WP (Call op) @ s; E {{ Φ }}.
Proof.
  iIntros "H". iApply wp_lift_atomic_step; [done|].
  iIntros (σ) "?". iMod ("H" with "[$]") as "[% H]".
  iSplitL "".
  {
    iModIntro; iPureIntro; destruct s => //= Herr.
      by apply bind_pure_no_err in Herr.
  }
  iIntros "!> * % !>".
  iIntros (σ2 efs Hstep).
  destruct Hstep as (?&?&Hstep&Hpure). inversion Hpure; subst.
  rewrite //= right_id.
  iApply "H"; eauto.
Qed.

Lemma wp_lift_pure_det_step {T} {s E Φ} E' (e1: proc OpT T) e2 efs :
  (if s is NotStuck then (∀ σ1, non_errorable e1 σ1) ∧ to_val e1 = None else to_val e1 = None) →
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

Lemma loop_non_errorable {T R} σ (b: T → proc OpT (LoopOutcome T R)) (init: T):
  non_errorable (Loop b init) σ.
Proof. inversion 1. Qed.

Lemma spawn_non_errorable {T} σ (e: proc OpT T):
  non_errorable (Spawn e) σ.
Proof.
  destruct σ. intros Herr. apply bind_pure_no_err in Herr.
  rewrite /fst_lift in Herr. inversion Herr. 
Qed.

Lemma wait_non_errorable σ:
  non_errorable (Wait) σ.
Proof.
  destruct σ. intros Herr. apply bind_pure_no_err in Herr.
  rewrite /fst_lift in Herr. inversion Herr. 
Qed.

Lemma unregister_non_errorable σ:
  non_errorable (Unregister) σ.
Proof.
  destruct σ. intros Herr. apply bind_pure_no_err in Herr.
  rewrite /fst_lift in Herr. inversion Herr. 
Qed.

Global Instance bind_proc_ctx {T R} (f: T → proc OpT R) : LanguageCtx Λ (λ x, Bind x f).
Proof.
  split; auto.
  - intros e1 σ ??? H.
    induction e1 => //=.
    * inversion H as (?&?&Hstep&Hpure).
      inversion Hpure; subst. repeat eexists; eauto.
    * do 2 eexists. destruct e1; split; eauto; try econstructor.
    * inversion H; subst; do 2 eexists; split; econstructor.
    * destruct σ as (n,s). destruct σ2 as (n2,s2).
      destruct H as ([]&?&?&?). inversion H0; subst.
      rewrite /fst_lift in H. destruct H; subst. inversion H. subst.
      eexists (Ret tt, []), (pred n, s2). split; try econstructor.
      do 2 eexists; last econstructor.
      rewrite /fst_lift; split; eauto.
    * destruct σ as (n,s). destruct σ2 as (n2,s2).
      destruct H as ([]&?&?&?). inversion H0; subst.
      rewrite /fst_lift in H. destruct H; subst. inversion H. subst.
      eexists (Ret tt, []), (1, s2). split; try econstructor.
      do 2 eexists; last econstructor.
      rewrite /fst_lift; split; eauto.
    * destruct σ as (n,s). destruct σ2 as (n2,s2).
      destruct H as ([]&?&?&?). inversion H0; subst.
      rewrite /fst_lift in H. destruct H; subst. inversion H. subst.
      eexists (Ret tt, [existT _ (Bind e1 (λ _, Unregister))]), (S n, s2). split; try econstructor.
      do 2 eexists; last econstructor.
      rewrite /fst_lift; split; eauto.
  - intros e1 σ1 Herr.
    induction e1 => //=.
    * apply bind_pure_no_err in Herr; intuition.
    * left. destruct e1; eauto; try econstructor.
    * apply bind_pure_no_err in Herr; intuition.
    * apply bind_pure_no_err in Herr; intuition.
    * apply bind_pure_no_err in Herr; intuition.
  - intros e1 σ ???? H.
    induction e1 => //=.
    * inversion H as (?&?&Hstep&Hpure).
      inversion Hpure; subst.
      inversion Hstep as (?&?&?&Hpure'); inversion Hpure'; subst.
      repeat eexists; eauto.
    * inversion H as ((?&?)&?&Hstep&Hpure).
      inversion Hpure; subst. eexists; split; eauto.
    * inversion H as ((?&?)&?&Hstep&Hpure).
      inversion Hpure; subst. eexists; split; eauto.
    * inversion H as ((?&?)&?&Hstep&Hpure).
      inversion Hpure; subst. eexists; split; eauto.
    * inversion H as ((?&?)&?&Hstep&Hpure).
      inversion Hpure; subst. eexists; split; eauto.
    * inversion H as ((?&?)&?&Hstep&Hpure).
      inversion Hpure; subst. eexists; split; eauto.
  - intros e1 σ ? Herr.
    induction e1 => //=.
    * do 2 apply bind_pure_no_err in Herr.
      eauto.
    * inversion Herr; eauto.
      destruct H1 as (?&?&?&Hp). inversion Hp.
    * inversion Herr.
      ** exfalso. eapply loop_non_errorable; eauto.
      ** destruct H1 as (?&?&?&Hp). inversion Hp.
    * inversion Herr.
      ** exfalso. eapply unregister_non_errorable; eauto.
      ** destruct H0 as (?&?&?&Hp). inversion Hp.
    * inversion Herr.
      ** exfalso. eapply wait_non_errorable; eauto.
      ** destruct H0 as (?&?&?&Hp). inversion Hp.
    * inversion Herr.
      ** exfalso. eapply spawn_non_errorable; eauto.
      ** destruct H0 as (?&?&?&Hp). inversion Hp.
Qed.

Global Instance id_ctx {T} : LanguageCtx Λ (fun (x : proc OpT T) => x).
Proof. split; intuition eauto. Qed.

Global Instance comp_ctx {T1 T2 T3} (K: proc OpT T1 → proc OpT T2) (K': proc OpT T2 → proc OpT T3) :
  LanguageCtx Λ K →
  LanguageCtx Λ K' →
  LanguageCtx Λ (λ x, K' (K x)).
Proof.
  intros Hctx Hctx'.
  split; intros.
  - by do 2 apply fill_not_val.
  - by do 2 apply fill_step_valid.
  - by do 2 apply fill_step_err.
  - edestruct (@fill_step_inv_valid _ _ _ _ _ Hctx'); eauto; intuition.
    { apply fill_not_val; auto. }
    subst.
    edestruct (@fill_step_inv_valid _ _ _ _ _ Hctx); eauto; intuition.
    subst.
    eauto.
  - do 2 (apply fill_step_inv_err; auto).
    { apply fill_not_val; auto. }
Qed.

Lemma wp_bind_proc {T1 T2} (f: T1 → proc OpT T2) s E (e: proc OpT T1) Φ :
  WP e @ s; E {{ v, WP Bind (of_val v) f @ s; E {{ Φ }} }} ⊢ WP Bind e f @ s; E {{ Φ }}.
Proof. by apply: wp_bind. Qed.

Lemma wp_bind_proc_val {T1 T2} (f: T1 → proc OpT T2) s E v Φ:
  ▷ WP f v @ s; E {{ v, Φ v }} -∗ WP Bind (of_val v) f @ s; E {{ v, Φ v }}.
Proof.
  iIntros "Hwp".
  iApply (wp_lift_step); first by auto.
  iIntros (σ1) "?".
  iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
  iSplitL "".
  { iPureIntro. destruct s; auto. inversion 1. }
  iIntros "!> !>". iIntros (??? Hstep); iFrame.
  iMod "Hclose". iModIntro; iFrame.
  inversion Hstep; subst; by iFrame.
Qed.

Lemma wp_bind_proc_subst {T1 T2} (f: T1 → proc OpT T2)  s E (e: proc OpT T1) Φ :
  WP e @ s; E {{ v, ▷ WP (f v) @ s; E {{ Φ }} }} ⊢ WP Bind e f @ s; E {{ Φ }}.
Proof.
  iIntros "H". iApply wp_bind_proc.
  iApply wp_wand_l; iFrame "H".
  iIntros (v).
  rewrite wp_bind_proc_val.
  (* TODO: something is being eta expanded here and so unification is failing *)
  replace (fun v : T2 => Φ v) with Φ by auto.
  eauto.
Qed.

Lemma wp_bind_proc_subst_weak {T1 T2} (f: T1 → proc OpT T2)  s E (e: proc OpT T1) Φ :
  WP e @ s; E {{ v, WP (f v) @ s; E {{ Φ }} }} ⊢ WP Bind e f @ s; E {{ Φ }}.
Proof.
  iIntros "H". iApply wp_bind_proc_subst.
  iApply wp_wand_l; iFrame "H"; eauto.
Qed.

Lemma wp_loop {T R} {s E Φ} (b: T → proc OpT (LoopOutcome T R)) (init: T):
  WP (b init) @ s; E {{ λ out, ▷ (WP (match out with
                                    | ContinueOutcome x => Loop b x
                                    | DoneWithOutcome r => Ret r
                                    end) @ s ; E {{ Φ }}) }}
  ⊢ WP (Loop b init) @ s; E {{ Φ }}.
Proof.
  iIntros "Hwp".
  iApply (wp_lift_pure_det_step E _ (loop1 b init)).
  { intros; destruct s; intuition eauto using loop_non_errorable. }
  - iIntros (σ1 e2 σ2 efs); inversion 1; subst; auto.
  - iIntros "!> !> !>"; iSplitR ""; auto.
    by iApply wp_bind_proc_subst.
Qed.

Global Instance Call_atomic {T} a (op: OpT T) : Atomic Λ a (Call op).
Proof.
  intros ???? (?&?&Hstep&Hpure); inversion Hpure; subst.
  destruct a; try econstructor; eauto.
Qed.

Global Instance Ret_atomic {T} (v: T)  : Atomic Λ a (Ret v).
Proof. intros ?????. inversion 1. Qed.

Global Instance Ret_IntoValue {T} (x: T) : IntoVal (Ret x : proc OpT T) x.
Proof. rewrite //=. Qed.

Lemma wp_ret {T} {s E Φ} (v: T) :
  Φ v ⊢ WP (Ret v) @ s; E {{ Φ }}.
Proof. iApply wp_value => //=. Qed.

(* We can no longer give a generic spawn lemma because it affects state *)
(*
Lemma wp_spawn {T} s E (e: proc OpT T) Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ tt -∗ WP Spawn e @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ".
  iApply wp_lift_pure_det_step.
  { destruct s; intuition. apply spawn_non_errorable. }
  { inversion 1; subst; split_and!; eauto. }
  iIntros "!> !> !> /="; iFrame.
  by iApply wp_value.
Qed.
*)

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

Ltac wp_ret := iApply wp_ret.
Ltac wp_bind := iApply wp_bind_proc_subst_weak.
Ltac wp_loop := iApply wp_loop.
