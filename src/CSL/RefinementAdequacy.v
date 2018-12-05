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

Theorem wp_recovery_refinement {T R} OpTa OpTc Σ (Λa: Layer OpTa) (Λc: Layer OpTc) `{invPreG Σ} s
        (ea: proc OpTa T) (ec: proc OpTc T) (rec: proc OpTc R)
        φ (absr: Λa.(State) → Λc.(State) → unit → Prop) E :
  nclose sourceN ⊆ E →
  (∀ (σ1a: Λa.(State)) σ1c,
      absr σ1a σ1c tt →
      (∀ `{Hinv : invG Σ} `{Hcfg: cfgG OpTa Λa Σ},
          (|={⊤}=> ∃ stateI : State Λc → iProp Σ,
             let _ : irisG OpTc Λc Σ := IrisG _ _ _ Hinv stateI in
             stateI σ1c ∗ source_ctx ([existT _ ea], σ1a)
               ∗ WP ec @ s; ⊤ {{ v, O ⤇ of_val v
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
       stateI σ1c' ∗ source_ctx (tp1', σ1a)
              ∗ WP rec @ s; ⊤ {{ v, (∀ σ2c, stateI σ2c ={⊤,E}=∗
                   ∃ σ2a σ2a', source_state σ2a ∗ ⌜Λa.(crash_step) σ2a σ2a' tt ∧ absr σ2a' σ2c tt⌝)}}
                              ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ ∃ tp σ2a, source_pool_map tp
                                         ∗ source_state σ2a ∗ ⌜φ tp σ2a σ2c⌝))%I) →
  crash_refines absr Λc ec (rec_singleton rec) (Λa.(exec) ea)
                (and_then (Λa.(exec_halt) ea) (fun _ => Λa.(crash_step))).
Proof.
  intros Hsub Hwp_e Hwp_rec.
  assert (∀ σ1a σ1c, absr σ1a σ1c tt → recv_adequate s ec rec σ1c
                          (λ v' σ2c', ∃ σ2a, exec Λa ea σ1a σ2a (existT _ v') ∧
                                             absr σ2a σ2c' tt)
                          (fun _ => True)).
  { intros.
    eapply wp_recovery_adequacy with
        (φinv := fun σ2c => ∃ tp2 tp2' σ2a efs, pool_map_incl tp2 tp2' ∧ φ tp2 σ2a σ2c
                                                ∧ exec_partial Λa ea σ1a σ2a tp2'); eauto.
    - iIntros (Hinv).
      assert (Inhabited Λa.(State)).
      { eexists; eauto. }
      iMod Hwp_e as (stateI) "[Hstate [#Hsrc [H Hφ]]]"; eauto.
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
    - admit.
  }
  split.
  - rewrite /refines.
    intros σ1a σ2c (T'&v) ([]&σ1c&Habsr&Hexec).
    edestruct H0; eauto.
    edestruct (recv_adequate_normal_result) as (v'&Heq_val&σ2a&HexecA&Habsr'); eauto.
    do 3 eexists; eauto.
    do 3 eexists; eauto.
    econstructor; eauto.
  -
Abort.