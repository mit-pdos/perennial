Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Abstraction.
Require Import Spec.Layer.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationTheorems.
Require Import Helpers.RelationRewriting.
Require Import CSL.WeakestPre CSL.Refinement CSL.Adequacy.
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
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ} s
        (ea: proc OpTa T) (ec: proc OpTc T) (rec: proc OpTc R)
        φ (absr: relation Λa.(State) Λc.(State) unit) E :
  nclose sourceN ⊆ E →
  (∀ (σ1a: Λa.(State)) σ1c,
      absr σ1a (Val σ1c tt) →
      (∀ `{Hinv : invG Σ} `{Hcfg: cfgG OpTa Λa Σ},
          (|={⊤}=> ∃ stateI : State Λc → iProp Σ,
             let _ : irisG OpTc Λc Σ := IrisG _ _ _ Hinv stateI in
             (source_ctx ([existT _ ea], σ1a) ∗ O ⤇ ea ∗ source_state σ1a) -∗
              stateI σ1c ∗ WP ec @ s; ⊤ {{ v, O ⤇ of_val v
                    ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ ∃ σ2a, source_state σ2a ∗ ⌜absr σ2a (Val σ2c tt)⌝)}}
                              ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ ∃ tp σ2a, source_pool_map tp
                                         ∗ source_state σ2a ∗ ⌜φ tp σ2a σ2c⌝))%I)) →
  (∀ `{Hinv : invG Σ} `{Hcfg: cfgG OpTa Λa Σ}
     tp1 tp1' σ1a σ1c σ1c'
     (Hφ: φ tp1 σ1a σ1c)
     (Htp_sub: pool_map_incl tp1 tp1')
     (Hcrash: Λc.(crash_step) σ1c (Val σ1c' tt)),
     (|={⊤}=> ∃ stateI : State Λc → iProp Σ,
       let _ : irisG OpTc Λc Σ := IrisG _ _ _ Hinv stateI in
       (source_ctx (tp1', σ1a) ∗ source_pool_map (tpool_to_map tp1') ∗ source_state σ1a) -∗
              stateI σ1c' ∗ WP rec @ s; ⊤ {{ v, (∀ σ2c, stateI σ2c ={⊤,E}=∗
                   ∃ σ2a σ2a', source_state σ2a ∗ ⌜Λa.(crash_step) σ2a (Val σ2a' tt)
                               ∧ absr σ2a' (Val σ2c tt)⌝)}}
                              ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ ∃ tp σ2a, source_pool_map tp
                                         ∗ source_state σ2a ∗ ⌜φ tp σ2a σ2c⌝))%I) →
  crash_refines absr Λc ec (rec_singleton rec) (Λa.(exec) ea)
                (and_then (Λa.(exec_halt) ea) (fun _ => Λa.(crash_step))).
Proof.
  intros Hsub Hwp_e Hwp_rec.
  assert (Hadeq: ∀ σ1a σ1c, absr σ1a (Val σ1c tt) → recv_adequate s ec rec σ1c
                          (λ v' σ2c', ∃ σ2a, exec Λa ea σ1a (Val σ2a (existT _ v')) ∧
                                             absr σ2a (Val σ2c' tt))
                          (λ σ2c', ∃ tp2 tp2' σ2a σ3a, pool_map_incl tp2 tp2' ∧
                                                   exec_partial Λa ea σ1a (Val σ2a tp2') ∧
                                                   crash_step Λa σ2a (Val σ3a tt) ∧
                                                   absr σ3a (Val σ2c' tt))).
  { intros.
    eapply wp_recovery_adequacy with
        (φinv := fun σ2c => ∃ tp2 tp2' σ2a, pool_map_incl tp2 tp2' ∧ φ tp2 σ2a σ2c
                                                ∧ exec_partial Λa ea σ1a (Val σ2a tp2')); eauto.
    - iIntros (Hinv).
      assert (Inhabited Λa.(State)).
      { eexists; eauto. }
      iMod (source_cfg_init [existT _ ea] σ1a) as (cfgG) "(#Hsrc&Hpool&HstateA)".
      iMod Hwp_e as (stateI) "Hwand"; eauto.
      iDestruct ("Hwand" with "[Hpool HstateA]") as "[Hstate [H Hφ]]"; eauto.
      { iFrame. iFrame "#".
        rewrite /source_pool_map/tpool_to_map fmap_insert fmap_empty insert_empty //=.
      }
      iExists stateI. iIntros "{$Hstate} !>".
      iSplitL "H".
      * iApply wp_wand_l; iFrame "H". iIntros (v') "[Hmapsto Hopen]".
        iIntros (σ2c') "Hstate".
        iMod ("Hopen" with "Hstate") as (σ2a) "(Hstate&%)".
        iInv "Hsrc" as (tp' σ') ">[Hauth Hp]" "_".
        iDestruct "Hp" as %Hp. rewrite //= in Hp.
        iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
        iDestruct (source_thread_reconcile with "Hmapsto Hauth") as %Hlookup; subst.
        apply take_drop_middle in Hlookup.

        iApply fupd_mask_weaken; first by set_solver+.
        iPureIntro. exists σ'; split; eauto.
        rewrite -Hlookup //= /of_val in Hp.
        eapply exec_partial_finish; eauto.
      * iIntros (σ2c') "Hstate".
        iMod ("Hφ" with "Hstate") as (tp2 σ2a) "(Hpool&Hstate&%)".
        iInv "Hsrc" as (tp' σ') ">[Hauth Hp]" "_".
        iDestruct "Hp" as %Hp. rewrite //= in Hp.
        iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
        iDestruct (source_pool_map_reconcile with "Hpool Hauth") as %Hpool; subst.

        iApply fupd_mask_weaken; first by set_solver+.
        iPureIntro. exists tp2, tp', σ'; split; eauto.
    - iIntros (Hinv).
      assert (Inhabited Λa.(State)).
      { eexists; eauto. }
      intros σ2c σ2c' (tp2&tp2'&σ2a&Hincl&Hφ&Hexec_partial) Hcrash.
      iMod (source_cfg_init tp2' σ2a) as (cfgG) "(#Hsrc&Hpool&HstateA)".
      iMod Hwp_rec as (stateI) "Hwand"; eauto.
      iDestruct ("Hwand" with "[$]") as "[Hstate [H Hφ]]"; eauto.
      iExists stateI. iIntros "{$Hstate} !>".
      iSplitL "H".
      * iApply wp_wand_l; iFrame "H". iIntros (v) "Hopen".
        iIntros (σ3c) "Hstate".
        iMod ("Hopen" with "Hstate") as (σ2a' σ3a) "(Hstate&%)".
        iInv "Hsrc" as (tp' σ') ">[Hauth Hp]" "_".
        iDestruct "Hp" as %Hp. rewrite //= in Hp.
        iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.

        iApply fupd_mask_weaken; first by set_solver+.
        iPureIntro. exists (tpool_to_map tp'), tp', σ', σ3a; split_and!; intuition eauto.
        { apply pool_map_incl_alt; reflexivity. }
        { eapply bind_star_trans; eauto. }
      * iIntros (σ3c) "Hstate".
        iMod ("Hφ" with "Hstate") as (tp3 σ3a) "(Hpool&Hstate&%)".
        iInv "Hsrc" as (tp' σ') ">[Hauth Hp]" "_".
        iDestruct "Hp" as %Hp. rewrite //= in Hp.
        iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
        iDestruct (source_pool_map_reconcile with "Hpool Hauth") as %Hpool; subst.

        iApply fupd_mask_weaken; first by set_solver+.
        iPureIntro. exists tp3, tp', σ'; split_and!; intuition eauto.
        { eapply bind_star_trans; eauto. }
  }
  split.
  - rewrite /refines.
    intros σ1a σ2c (T'&v) ([]&σ1c&Habsr&Hexec).
    edestruct Hadeq; eauto.
    edestruct (recv_adequate_normal_result) as (v'&Heq_val&σ2a&HexecA&Habsr'); eauto.
    do 3 eexists; eauto.
    do 3 eexists; eauto.
    econstructor; eauto.
  - rewrite /refines.
    intros σ1a σ2c [] ([]&σ1c&Habsr&Hexec).
    edestruct Hadeq; eauto.
    edestruct (recv_adequate_result) as (v'&?&σ2a&?&?&HexecA&HcrashA&Habsr'); eauto.
    do 3 eexists; eauto.
    do 3 eexists; eauto.
    * unshelve (do 3 eexists; eauto); try exact tt.
      econstructor; eauto.
    * unshelve (do 3 eexists; eauto); try exact tt.
      econstructor; eauto.
Qed.

Theorem wp_recovery_trace_refinement {T R} OpTa OpTc Σ (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ} s
        (ea: proc OpTa T) (ec: proc OpTc T) (rec: proc OpTc R)
        φ (absr: Λa.(State) → Λc.(State) → unit → Prop) E :
  nclose sourceN ⊆ E →
  (∀ (σ1a: Λa.(State)) σ1c,
      absr σ1a σ1c tt →
      (∀ `{Hinv : invG Σ} `{Hcfg: cfgG OpTa Λa Σ},
          (|={⊤}=> ∃ stateI : State Λc → iProp Σ,
             let _ : irisG OpTc Λc Σ := IrisG _ _ _ Hinv stateI in
             (source_ctx ([existT _ ea], σ1a) ∗ O ⤇ ea ∗ source_state σ1a) -∗
              stateI σ1c ∗ WP ec @ s; ⊤ {{ v, O ⤇ of_val v
                    ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ ∃ σ2a, source_state σ2a ∗ ⌜absr σ2a σ2c tt⌝)}}
                              ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ ∃ tp σ2a, source_pool_map tp
                                         ∗ source_state σ2a ∗ ⌜φ tp σ2a σ2c⌝))%I)) →
  (∀ `{Hinv : invG Σ} `{Hcfg: cfgG OpTa Λa Σ}
     tp1 tp1' σ1a σ1c σ1c'
     (Hφ: φ tp1 σ1a σ1c)
     (Htp_sub: pool_map_incl tp1 tp1')
     (Hcrash: Λc.(crash_step) σ1c σ1c' tt),
     (|={⊤}=> ∃ stateI : State Λc → iProp Σ,
       let _ : irisG OpTc Λc Σ := IrisG _ _ _ Hinv stateI in
       (source_ctx (tp1', σ1a) ∗ source_pool_map (tpool_to_map tp1') ∗ source_state σ1a) -∗
              stateI σ1c' ∗ WP rec @ s; ⊤ {{ v, (∀ σ2c, stateI σ2c ={⊤,E}=∗
                   ∃ σ2a σ2a', source_state σ2a ∗ ⌜Λa.(crash_step) σ2a σ2a' tt ∧ absr σ2a' σ2c tt⌝)}}
                              ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ ∃ tp σ2a, source_pool_map tp
                                         ∗ source_state σ2a ∗ ⌜φ tp σ2a σ2c⌝))%I) →
  (∀ tp σa σc, φ tp σa σc → trace_relation _ _ σa σc tt) →
  halt_refines absr Λc (trace_relation Λc Λa)
                 ec
                 (rec_singleton rec) (Λa.(exec_halt) ea)
                 (and_then (Λa.(exec_halt) ea) (fun _ => Λa.(crash_step))).
Proof.
  intros Hsub Hwp_e Hwp_rec Hφ_trace.
  apply halt_refines_trace_relation_alt.
  rewrite /halt_refines/refines_if.
  intros σ1a σ2c_outer [] ([]&σ1c_outer&Habsr&Hexec).
  eapply wp_recovery_invariance with
        (ρ := fun σ2c => (v <- _ <- exec_halt Λa ea;
            Λa.(crash_step); _ <- trace_relation Λc Λa; pure v) σ1a σ2c ())
        (φinv := fun σ2c => ∃ tp2 tp2' σ2a, pool_map_incl tp2 tp2' ∧ φ tp2 σ2a σ2c
                                                ∧ exec_partial Λa ea σ1a σ2a tp2'); eauto.
  - iIntros (Hinv).
    assert (Inhabited Λa.(State)).
    { eexists; eauto. }
    iMod (source_cfg_init [existT _ ea] σ1a) as (cfgG) "(#Hsrc&Hpool&HstateA)".
    iMod Hwp_e as (stateI) "Hwand"; eauto.
    iDestruct ("Hwand" with "[Hpool HstateA]") as "[Hstate [H Hφ]]"; eauto.
    { iFrame. iFrame "#".
      rewrite /source_pool_map/tpool_to_map fmap_insert fmap_empty insert_empty //=.
    }
    iExists stateI. iIntros "{$Hstate} !>".
    iSplitL "H".
    * iApply wp_wand_l; iFrame "H"; auto.
    * iIntros (σ2c') "Hstate".
      iMod ("Hφ" with "Hstate") as (tp2 σ2a) "(Hpool&Hstate&%)".
      iInv "Hsrc" as (tp' σ') ">[Hauth Hp]" "_".
      iDestruct "Hp" as %Hp. rewrite //= in Hp.
      iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
      iDestruct (source_pool_map_reconcile with "Hpool Hauth") as %Hpool; subst.

      iApply fupd_mask_weaken; first by set_solver+.
      iPureIntro. exists tp2, tp', σ'; split; eauto.
  - iIntros (Hinv).
    assert (Inhabited Λa.(State)).
    { eexists; eauto. }
    intros σ2c σ2c' (tp2&tp2'&σ2a&Hincl&Hφ&Hexec_partial) Hcrash.
    iMod (source_cfg_init tp2' σ2a) as (cfgG) "(#Hsrc&Hpool&HstateA)".
    iMod Hwp_rec as (stateI) "Hwand"; eauto.
    iDestruct ("Hwand" with "[$]") as "[Hstate [H Hφ]]"; eauto.
    iExists stateI. iIntros "{$Hstate} !>".
    iSplitL "H".
    * iApply wp_wand_l; iFrame "H"; eauto.
    * iIntros (σ3c) "Hstate".
      iMod ("Hφ" with "Hstate") as (tp3 σ3a) "(Hpool&Hstate&%)".
      iInv "Hsrc" as (tp' σ') ">[Hauth Hp]" "_".
      iDestruct "Hp" as %Hp. rewrite //= in Hp.
      iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
      iDestruct (source_pool_map_reconcile with "Hpool Hauth") as %Hpool; subst.

      iApply fupd_mask_weaken; first by set_solver+.
      iPureIntro. exists tp3, tp', σ'; split_and!; intuition eauto.
      { eapply bind_star_trans; eauto. }
  - intros σ (tp2&tp2'&σ2a&Hincl&?&Hexec').
    edestruct (crash_total _ σ2a) as (σ2a'&?).
    do 3 eexists.
    { do 3 eexists; eauto.
      do 3 eexists; eauto.
      econstructor; eauto.
    }
    eexists tt, _; split; last by econstructor.
    transitivity (trace_proj _ σ2a).
    { symmetry. eapply crash_preserves_trace; eauto. }
    { eapply Hφ_trace; eauto. }
  - intros σ1c σ2c (tp2&tp2'&σ2a&Hincl&Hφ&Hexec') Hcrash.
    edestruct (crash_total _ σ2a) as (σ2a'&?).
    do 3 eexists.
    { do 3 eexists; eauto.
      do 3 eexists; eauto.
      econstructor; eauto.
    }
    eexists tt, _; split; last by econstructor.
    transitivity (trace_proj _ σ2a).
    { symmetry. eapply crash_preserves_trace; eauto. }
    transitivity (trace_proj _ σ1c).
    { eapply Hφ_trace; eauto. }
    { eapply crash_preserves_trace; eauto. }
Qed.
