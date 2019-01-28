Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Abstraction.
Require Import Spec.Layer.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationTheorems.
Require Import Helpers.RelationRewriting.
Require Export CSL.WeakestPre CSL.Refinement CSL.Adequacy.
From iris.algebra Require Import auth frac agree gmap list.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
Unset Implicit Arguments.

Import RelationNotations.
Definition pool_map_incl {OpT} (tp1: gmap nat (@procT OpT)) (tp2: thread_pool OpT) :=
  ∀ j e, tp1 !! j = Some e → tp2 !! j = Some e.

Lemma pool_map_incl_alt {OpT} tp1 (tp2: thread_pool OpT) :
  pool_map_incl tp1 tp2 ↔ tp1 ⊆ tpool_to_map tp2.
Proof.
  split.
  - intros Hincl j.
    rewrite /option_relation.
    specialize (Hincl j). destruct (tp1 !! j) as [p|].
    * rewrite (proj2 (tpool_to_map_lookup tp2 j p)); eauto.
    * destruct (tpool_to_map tp2 !! j); eauto.
  - intros Hincl j e Hin.
    apply tpool_to_map_lookup.
    specialize (Hincl j). rewrite Hin //= in Hincl.
    destruct (tpool_to_map tp2 !! j); eauto; [ congruence | contradiction ].
Qed.

Require Import Helpers.RelationAlgebra.
Theorem wp_recovery_crash_refinement {T R} OpTa OpTc Σ (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (ea: proc OpTa T) (ec: proc OpTc T) (rec: proc OpTc R)
        (φinv : forall {_ : @cfgG OpTa Λa Σ}, Λc.(State) → iProp Σ)
        (absr: relation Λa.(State) Λc.(State) unit) E
        (Habsr_no_err: ∀ σa, ¬ absr σa Err):
  nclose sourceN ⊆ E →
  (∀ (σ1a: Λa.(State)) σ1c,
      absr σ1a (Val σ1c tt) →
      (∀ `{Hinv : invG Σ} `{Hcfg: cfgG OpTa Λa Σ},
          (|={⊤}=> ∃ stateI : State Λc → iProp Σ,
             let _ : irisG OpTc Λc Σ := IrisG _ _ _ Hinv stateI in
             (source_ctx ([existT _ ea], σ1a) ∗ O ⤇ ea ∗ source_state σ1a)
               ={⊤}=∗
               stateI σ1c
               ∗ WP ec @ NotStuck; ⊤ {{ v, O ⤇ of_val v
                    ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ ∃ σ2a, source_state σ2a ∗ ⌜absr σ2a (Val σ2c tt)⌝)}}
                                     ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ φinv σ2c)
        ∗
        □ (∀ `{Hinv : invG Σ} `{Hcfg: cfgG OpTa Λa Σ} σ1c σ1c'
           (Hcrash: Λc.(crash_step) σ1c (Val σ1c' tt)),
            (φinv σ1c ={⊤}=∗ ∃ stateI : State Λc → iProp Σ,
               let _ : irisG OpTc Λc Σ := IrisG _ _ _ Hinv stateI in
               stateI σ1c'
               ∗ WP rec @ NotStuck; ⊤ {{ v, (∀ σ2c, stateI σ2c ={⊤,E}=∗
                   ∃ σ2a σ2a', source_state σ2a ∗ ⌜Λa.(crash_step) σ2a (Val σ2a' tt)
                               ∧ absr σ2a' (Val σ2c tt)⌝)}}
                                     ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ φinv σ2c)))))%I) →
  crash_refines absr Λc ec (rec_singleton rec) (Λa.(exec) ea)
                (and_then (Λa.(exec_halt) ea) (fun _ => Λa.(crash_step))).
Proof.
  intros Hsub Hwp.
  assert (Hno_fault_cut :
            ∀ σ1a, ¬ (v <- exec Λa ea; _ <- absr; pure v) σ1a Err ->
                   ¬ exec Λa ea σ1a Err).
  { clear. intros σ1a Hno_err.
    intros Hexec. apply Hno_err.
    left; auto.
  }
  assert (Hno_fault_cut':
            ∀ σ1a, ¬ (v <- _ <- exec_halt Λa ea;
                          Λa.(crash_step); _ <- absr; pure v) σ1a Err ->
                   ¬ exec Λa ea σ1a Err).
  { clear. intros σ1a Hno_err.
    intros Hexec. apply Hno_err. do 3 left. apply exec_partial_err_exec_err; eauto.
  }
  assert (Hadeq: ∀ σ1a σ1c (Hno_fault : ¬  exec Λa ea σ1a Err),
             absr σ1a (Val σ1c tt) → recv_adequate NotStuck ec rec σ1c
                          (λ v' σ2c', ∃ σ2a, exec Λa ea σ1a (Val σ2a (existT _ v')) ∧
                                             absr σ2a (Val σ2c' tt))
                          (λ σ2c', ∃ tp2 σ2a σ3a, exec_partial Λa ea σ1a (Val σ2a tp2) ∧
                                                   crash_step Λa σ2a (Val σ3a tt) ∧
                                                   absr σ3a (Val σ2c' tt))).
  { intros σ1a σ1c ? Habsr_init.
    eapply wp_recovery_adequacy with
        (φinv0 := fun σ => (∃ _ : cfgG Σ, φinv _ σ ∗ source_inv [existT T ea] σ1a)%I); eauto.
    iIntros (Hinv).
    assert (Inhabited Λa.(State)).
    { eexists; eauto. }
    iMod (source_cfg_init [existT _ ea] σ1a) as (cfgG) "(#Hsrc&Hpool&HstateA)"; auto.
    { intros Herr; apply Hno_fault. apply exec_partial_err_exec_err; eauto. }
    iPoseProof (Hwp _ _ Habsr_init $! Hinv cfgG) as "H".
    iMod "H" as (stateI) "Hwand"; eauto.
    iMod ("Hwand" with "[Hpool HstateA]") as "[Hstate [H [Hinv #Hφ]]]"; eauto.
    { iFrame. iFrame "#".
      rewrite /source_pool_map/tpool_to_map fmap_insert fmap_empty insert_empty //=.
    }
    iExists stateI. iIntros "{$Hstate} !>".
    iSplitL "H"; last iSplitL "Hinv".
    * iApply wp_wand_l; iFrame "H". iIntros (v') "[Hmapsto Hopen]".
      iIntros (σ2c') "Hstate".
      iMod ("Hopen" with "Hstate") as (σ2a) "(Hstate&%)".
      iInv "Hsrc" as (tp' σ') ">[Hauth Hp]" "_".
      iDestruct "Hp" as %Hp. destruct Hp as (Hp&Hno_fault'). rewrite //= in Hp.
      iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
      iDestruct (source_thread_reconcile with "Hmapsto Hauth") as %Hlookup; subst.
      apply take_drop_middle in Hlookup.

      iApply fupd_mask_weaken; first by set_solver+.
      iPureIntro. exists σ'; split; eauto.
      rewrite -Hlookup //= /of_val in Hp.
      eapply exec_partial_finish; eauto.
    * iIntros. iMod ("Hinv" with "[$]").
      iMod (inv_open_timeless with "Hsrc") as "(?&_)"; first by eassumption.
      iApply fupd_mask_weaken; auto.
      { set_solver+. }
      iFrame. iExists _; iFrame.
    * iModIntro. iIntros (????) "Hinv".
      iDestruct "Hinv" as (cfgG') "(?&HcfgInv)".
      iClear "Hsrc".
      iMod ("Hφ" with "[//] [$]") as (stateI') "(Hstate&Hwp&Hinv)".
      iMod (inv_alloc sourceN ⊤ (source_inv _ _) with "HcfgInv") as "#cfgInv".
      iModIntro. iExists stateI'. iFrame.
      iSplitL "Hwp".
      ** iApply wp_wand_l; iFrame.
         iIntros (_) "H1".
         iIntros (σ) "Hstate".
         iMod ("H1" with "[$]") as (σ2a σ3a) "(Hstate&Hp)".
         iDestruct "Hp" as %(Hcrash&Habsr).
         iMod (inv_open_timeless with "cfgInv") as "(Hinv&_)"; first by eassumption.
         iApply fupd_mask_weaken; auto.
         { set_solver+. }
         iDestruct "Hinv" as (tp' σ3a') "(Hauth&%&%)".
         iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
         iPureIntro. eexists _, _, _. intuition; eauto.
      ** iIntros. iMod ("Hinv" with "[$]").
         iMod (inv_open_timeless with "cfgInv") as "(?&_)"; first by eassumption.
         iApply fupd_mask_weaken; auto.
         { set_solver+. }
         iFrame. iExists _; iFrame.
  }
  split.
  - rewrite /refines.
    apply rimpl_alt.
    intros σ1a [σ2c (T'&v) |] Hno_fault; last first.
    {
      intros Hfalse; exfalso.
      destruct Hfalse as [|([]&?&?&?)]; eauto.
      { eapply Habsr_no_err; eauto. }
      edestruct Hadeq; eauto.
      eapply recv_adequate_not_stuck; eauto.
      apply exec_err_rexec_err; eauto.
    }
    intros ([]&σ1c&Habsr&Hexec).
    edestruct Hadeq; eauto.
    edestruct (recv_adequate_normal_result) as (v'&Heq_val&σ2a&HexecA&Habsr'); eauto.
    do 3 eexists; eauto.
    do 3 eexists; eauto.
    rewrite Heq_val. econstructor.
  - rewrite /refines.
    apply rimpl_alt.
    intros σ1a [σ2c [] |] Hno_fault; last first.
    {
      intros Hfalse; exfalso.
      destruct Hfalse as [|([]&?&?&?)]; eauto.
      { eapply Habsr_no_err; eauto. }
      edestruct Hadeq; eauto.
      eapply recv_adequate_not_stuck; eauto.
    }
    intros ([]&σ1c&Habsr&Hexec).
    edestruct Hadeq; eauto.
    edestruct (recv_adequate_result) as (tp2&σ2a&?&HexecA&HcrashA&Habsr'); eauto.
    do 3 eexists; eauto.
    do 3 eexists; eauto.
    * unshelve (do 3 eexists; eauto); try exact tt.
      econstructor; eauto.
    * unshelve (do 3 eexists; eauto); try exact tt.
      econstructor; eauto.
Qed.

(* TODO: need to generalize so that φinv can depend on cfgG as above *)
Theorem wp_recovery_trace_refinement {T R} OpTa OpTc Σ (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (ea: proc OpTa T) (ec: proc OpTc T) (rec: proc OpTc R)
        φinv (absr: relation Λa.(State) Λc.(State) unit) E
        (Habsr_no_err: ∀ σa, ¬ absr σa Err):
  nclose sourceN ⊆ E →
  (∀ (σ1a: Λa.(State)) σ1c,
      absr σ1a (Val σ1c tt) →
      (∀ `{Hinv : invG Σ} `{Hcfg: cfgG OpTa Λa Σ},
          (|={⊤}=> ∃ stateI : State Λc → iProp Σ,
             let _ : irisG OpTc Λc Σ := IrisG _ _ _ Hinv stateI in
             (source_ctx ([existT _ ea], σ1a) ∗ O ⤇ ea ∗ source_state σ1a)
               ={⊤}=∗
               stateI σ1c
               ∗ WP ec @ NotStuck; ⊤ {{ v, O ⤇ of_val v
                    ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ ∃ σ2a, source_state σ2a ∗ ⌜absr σ2a (Val σ2c tt)⌝)}}
                                      ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ φinv σ2c
                                                ∗ ∃ σ2a, source_state σ2a
                                                     ∗ ⌜ trace_relation _ _ σ2a (Val σ2c tt) ⌝)
        ∗
        □ (∀ `{Hinv : invG Σ} `{Hcfg: cfgG OpTa Λa Σ} σ1c σ1c'
           (Hcrash: Λc.(crash_step) σ1c (Val σ1c' tt)),
            (φinv σ1c ={⊤}=∗ ∃ stateI : State Λc → iProp Σ,
               let _ : irisG OpTc Λc Σ := IrisG _ _ _ Hinv stateI in
               stateI σ1c'
               ∗ WP rec @ NotStuck; ⊤ {{ v, (∀ σ2c, stateI σ2c ={⊤,E}=∗
                   ∃ σ2a σ2a', source_state σ2a ∗ ⌜Λa.(crash_step) σ2a (Val σ2a' tt)
                               ∧ absr σ2a' (Val σ2c tt)⌝)}}
                                      ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ φinv σ2c
                                                ∗ ∃ σ2a, source_state σ2a
                                                     ∗ ⌜ trace_relation _ _ σ2a (Val σ2c tt) ⌝)))))%I)
    →
  halt_refines absr Λc (trace_relation Λc Λa)
                 ec
                 (rec_singleton rec) (Λa.(exec_halt) ea)
                 (and_then (Λa.(exec_halt) ea) (fun _ => Λa.(crash_step))).
Proof.
  intros Hsub Hwp.
  apply halt_refines_trace_relation_alt; eauto.
  rewrite /halt_refines/refines_if.
  assert (Hno_fault_cut :
            ∀ σ1a, ¬ (v <- exec Λa ea; _ <- absr; pure v) σ1a Err ->
                   ¬ exec Λa ea σ1a Err).
  { clear. intros σ1a Hno_err.
    intros Hexec. apply Hno_err.
    left; auto.
  }
  assert (Hno_fault_cut':
            ∀ σ1a, ¬ (v <- _ <- exec_halt Λa ea;
                          Λa.(crash_step); _ <- trace_relation Λc Λa; pure v) σ1a Err ->
                   ¬ exec Λa ea σ1a Err).
  { clear. intros σ1a Hno_err.
    intros Hexec. apply Hno_err. do 3 left. apply exec_partial_err_exec_err; eauto.
  }
  apply rimpl_alt.
  intros σ1a ret Hno_fault Hstep.
  assert (∃ σ1c_outer,
             absr σ1a (Val σ1c_outer ()) ∧
             rexec_partial Λc ec (rec_singleton rec) σ1c_outer ret)
         as (σ1c_outer&Habsr_init&Hexec).
  {
    destruct ret.
    - destruct Hstep as ([]&?&?&?). eexists; split; eauto.
    - destruct Hstep as [|([]&?&?&?)].
      * exfalso. eapply Habsr_no_err; eauto.
      * eauto.
  }
  edestruct @wp_recovery_invariance with
        (ρ := fun σ2c => (v <- _ <- exec_halt Λa ea;
            Λa.(crash_step); _ <- trace_relation Λc Λa; pure v) σ1a (Val σ2c ()))
        (φ := fun (_ : T) (_ : Λc.(State)) => True)
        (φrec := fun (_ : Λc.(State)) => True)
        (φinv := fun σ => (φinv σ ∗ ∃ _ : cfgG Σ, source_inv [existT T ea] σ1a)%I)
        as (Hρ&Hadeq); eauto.
  {
    iIntros (Hinv).
    assert (Inhabited Λa.(State)).
    { eexists; eauto. }
    iMod (source_cfg_init [existT _ ea] σ1a) as (cfgG) "(#Hsrc&Hpool&HstateA)"; auto.
    { intros Herr. eapply Hno_fault_cut'; first eapply Hno_fault.
      apply exec_partial_err_exec_err; eauto. }
    iPoseProof (Hwp _ _ Habsr_init $! Hinv cfgG) as "H".
    iMod "H" as (stateI) "Hwand"; eauto.
    iMod ("Hwand" with "[Hpool HstateA]") as "[Hstate [H [Hinv #Hφ]]]"; eauto.
    { iFrame. iFrame "#".
      rewrite /source_pool_map/tpool_to_map fmap_insert fmap_empty insert_empty //=.
    }
    iExists stateI. iIntros "{$Hstate} !>".
    iSplitL "H"; last iSplitL "Hinv".
    * iApply wp_wand_l; iFrame "H". iIntros (v') "[Hmapsto Hopen]".
      iIntros (σ2c') "Hstate".
      iMod ("Hopen" with "Hstate") as (σ2a) "(Hstate&%)".
      iInv "Hsrc" as (tp' σ') ">[Hauth Hp]" "_".
      iDestruct "Hp" as %Hp. destruct Hp as (Hp&Hno_fault'). rewrite //= in Hp.
      iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
      iDestruct (source_thread_reconcile with "Hmapsto Hauth") as %Hlookup; subst.
      apply take_drop_middle in Hlookup.

      iApply fupd_mask_weaken; first by set_solver+.
      iPureIntro; auto.
    * iIntros.
      iMod ("Hinv" with "[$]") as "(Hφinv&Hrest)".
      iDestruct "Hrest" as (σ2a) "(Hstate&Htrace)". iDestruct "Htrace" as %Htrace.
      iMod (inv_open_timeless with "Hsrc") as "(Hinv&_)"; first by eassumption.
      iApply fupd_mask_weaken; auto.
      { set_solver+. }
      iDestruct "Hinv" as (tp' σ3a') "(Hauth&%&%)".
      iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
      iFrame. iSplit.
      ** iExists _, _; eauto.
      ** iPureIntro.
         edestruct (crash_total _ σ3a') as (σ3a''&?).
         do 3 eexists.
         { do 3 eexists; eauto.
           do 3 eexists; eauto.
           econstructor; eauto.
         }
         eexists tt, _; split; last by econstructor.
         eexists; split; eauto.
         transitivity (trace_proj _ σ3a').
         { symmetry. eapply crash_preserves_trace; eauto. }
         { inversion Htrace as (?&Heq&?). inversion Heq; subst; eauto. }
    * iModIntro. iIntros (????) "(?&Hinv)".
      iDestruct "Hinv" as (cfgG') "HcfgInv".
      iClear "Hsrc".
      iMod ("Hφ" with "[//] [$]") as (stateI') "(Hstate&Hwp&Hinv)".
      iMod (inv_alloc sourceN ⊤ (source_inv _ _) with "HcfgInv") as "#cfgInv".
      iModIntro. iExists stateI'. iFrame.
      iSplitL "Hwp".
      ** iApply wp_wand_l; iFrame.
         iIntros (_) "H1".
         iIntros (σ) "Hstate".
         iMod ("H1" with "[$]") as (σ2a σ3a) "(Hstate&Hp)".
         iDestruct "Hp" as %(Hcrash&Habsr).
         iMod (inv_open_timeless with "cfgInv") as "(Hinv&_)"; first by eassumption.
         iApply fupd_mask_weaken; auto.
         { set_solver+. }
      ** iIntros.
         iMod ("Hinv" with "[$]") as "(Hφinv&Hrest)".
         iDestruct "Hrest" as (σ2a) "(Hstate&Htrace)". iDestruct "Htrace" as %Htrace.
         iMod (inv_open_timeless with "cfgInv") as "(Hinv&_)"; first by eassumption.
         iApply fupd_mask_weaken; auto.
         { set_solver+. }
         iDestruct "Hinv" as (tp' σ3a') "(Hauth&%&%)".
         iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
         iFrame. iSplit.
         *** iExists _, _; eauto.
         *** iPureIntro.
         edestruct (crash_total _ σ3a') as (σ3a''&?).
         do 3 eexists.
         { do 3 eexists; eauto.
           do 3 eexists; eauto.
           econstructor; eauto.
         }
         eexists tt, _; split; last by econstructor.
         eexists; split; eauto.
         transitivity (trace_proj _ σ3a').
         { symmetry. eapply crash_preserves_trace; eauto. }
         { inversion Htrace as (?&Heq&?). inversion Heq; subst; eauto. }
  }
  destruct ret as [? []|]; eauto.
  exfalso. eapply recv_adequate_not_stuck; eauto using rexec_partial_err_rexec_err.
Qed.
