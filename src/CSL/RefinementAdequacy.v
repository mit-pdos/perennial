From Transitions Require Import Relations Rewriting.

Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Layer.
Require Export CSL.WeakestPre CSL.Refinement CSL.Adequacy.
From iris.algebra Require Import auth frac agree gmap list.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
Unset Implicit Arguments.

Import RelationNotations.
From Transitions Require Import Relations.

Definition wp_recovery_refinement {Ta Tc R OpTa OpTc} Σ (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (ea: proc OpTa Ta) (ec: proc OpTc Tc) (rec: proc OpTc R) (σ1a: State Λa) σ1c φ φrec E k :=
  Nat.iter k (λ P, |==> ▷ P)%I
    ((⌜ nclose sourceN ⊆ E ⌝ ∧
             ∃ (φinv : forall {_ : @cfgG OpTa Λa Σ}, State Λc → iProp Σ),
         ∀ `{Hinv : invG Σ} `{Hcfg: cfgG OpTa Λa Σ},
          (|={⊤}=> ∃ stateI : State Λc → iProp Σ,
             let _ : irisG OpTc Λc Σ := IrisG _ _ _ Hinv stateI in
             (source_ctx' ([existT _ ea], (snd σ1a)) ∗ O ⤇ ea ∗ source_state (snd σ1a))
               ={⊤}=∗
               stateI σ1c
               ∗ WP ec @ NotStuck; ⊤ {{ vc, ∃ (va: Ta), O ⤇ of_val va
                    ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ ∃ σ2a, source_state σ2a ∗ φ va vc σ2a (snd σ2c))}}
                    ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ φinv σ2c)
        ∗
        □ (∀ `{Hinv : invG Σ} `{Hcfg: cfgG OpTa Λa Σ} σ1c σ1c'
           (Hcrash: lifted_crash_step Λc σ1c (Val σ1c' tt)),
            (φinv σ1c ∗ source_ctx' ([existT _ ea], (snd σ1a)) ={⊤}=∗ ∃ stateI : State Λc → iProp Σ,
               let _ : irisG OpTc Λc Σ := IrisG _ _ _ Hinv stateI in
               stateI σ1c'
               ∗ WP rec @ NotStuck; ⊤ {{ v, (∀ σ2c, stateI σ2c ={⊤,E}=∗
                   ∃ σ2a σ2a', source_state (snd σ2a) ∗ ⌜lifted_crash_step Λa σ2a (Val σ2a' tt) ⌝ ∗
                               φrec (snd σ2a') (snd σ2c) )}}
               ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ φinv σ2c))))))%I.


Fixpoint wp_proc_seq_refinement {Ta Tc R OpTa OpTc} {Σ} (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (esa: proc_seq OpTa Ta) (esc: proc_seq OpTc Tc) (rec: proc OpTc R)
        (σ1a: State Λa) σ1c φ E {struct esa} : iProp Σ :=
  match esa, esc with
  | Proc_Seq_Nil va, Proc_Seq_Nil vc => (φ va vc σ1a σ1c)%I
  | @Proc_Seq_Bind _ _ T0a ea esa,
    @Proc_Seq_Bind _ _ T0c ec esc =>
    wp_recovery_refinement Σ Λa Λc ea ec rec σ1a σ1c
      (λ (va: T0a) (vc: T0c)  σ2a σ2c, ∀ σ2c' (Hfinish: Λc.(finish_step) σ2c (Val σ2c' tt)),
          ∃ σ2a' (Hfinisha: Λa.(finish_step) σ2a (Val σ2a' tt)),
          wp_proc_seq_refinement Λa Λc (esa (Normal (existT T0a va)))
                                       (esc (Normal (existT T0c vc)))
                                         rec (1, σ2a') (1, σ2c') φ E)%I
      (λ σ2a σ2c, wp_proc_seq_refinement Λa Λc (esa (Recovered (existT _ tt)))
                                         (esc (Recovered (existT _ tt)))
                                         rec (1, σ2a) (1, σ2c) φ E) E O
  | _, _ => False%I
  end.

Lemma crash_step_snd {OpT} (Λa: Layer OpT) σ1a σ2a t n:
  lifted_crash_step Λa σ1a (Val σ2a t) →
  lifted_crash_step Λa (n, snd σ1a) (Val (1, snd σ2a) tt).
Proof.
  rewrite /lifted_crash_step.
  destruct σ1a as (n1&σ1a).
  destruct σ2a as (n2&σ2a).
  intros ([]&(?&σ1a')&Hput&Hcrash).
  inversion Hput; subst.
  inversion H. subst.
  inversion Hcrash; subst.
  exists tt, (1, σ1a').
  split; eauto. econstructor; destruct t; eauto.
Qed.

Lemma finish_step_snd {OpT} (Λa: Layer OpT) σ1a σ2a t n:
  lifted_finish_step Λa σ1a (Val σ2a t) →
  lifted_finish_step Λa (n, snd σ1a) (Val (1, snd σ2a) tt).
Proof.
  rewrite /lifted_finish_step.
  destruct σ1a as (n1&σ1a).
  destruct σ2a as (n2&σ2a).
  intros ([]&(?&σ1a')&Hput&Hcrash).
  inversion Hput; subst.
  inversion H. subst.
  inversion Hcrash; subst.
  exists tt, (1, σ1a').
  split; eauto. econstructor; destruct t; eauto.
Qed.

Lemma lifted_finish_step_intro {OpT} (Λa: Layer OpT) n σ σ' t1 t2:
 finish_step Λa σ (Val σ' t1) →
 lifted_finish_step Λa (n, σ) (Val (1, σ') t2).
Proof.
  intros. destruct t1, t2.
  exists tt, (1, σ); split; rewrite //=.
Qed.

Lemma lifted_finish_step_intro' {OpT} (Λa: Layer OpT) σ σ' t1 t2:
 finish_step Λa (snd σ) (Val σ' t1) →
 lifted_finish_step Λa σ (Val (1, σ') t2).
Proof.
  intros. destruct t1, t2, σ.
  eapply lifted_finish_step_intro; eauto.
Qed.

Lemma wp_recovery_refinement_impl_wp_recovery {Ta Tc R} OpTa OpTc Σ (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (ea: proc OpTa Ta) (ec: proc OpTc Tc) (rec: proc OpTc R) σ1a σ1c φ φrec E k
        (Hno_fault : ¬ exec Λa ea (1, σ1a) Err):
  wp_recovery_refinement Σ Λa Λc ea ec rec (1, σ1a) σ1c φ φrec E k ⊢
  wp_recovery NotStuck ec rec σ1c
    (λ (vc : Tc) (σ2c : State Λc),
       ∃ va σ2a, ⌜exec Λa ea (1, σ1a) (Val σ2a (existT Ta va))⌝ ∗ φ va vc σ2a.2 σ2c.2)
    (λ σ2c : State Λc,
       ∃ tp2 (σ2a σ2a' : Proc.State),
         ⌜exec_partial Λa ea (1, σ1a) (Val σ2a tp2) ∧ lifted_crash_step Λa σ2a (Val σ2a' tt)⌝
         ∗ φrec σ2a'.2 σ2c.2) k.
Proof.
  iIntros "Hwp".
  iApply (bupd_iter_mono with "[] Hwp"). iIntros "Hwp".
  iDestruct "Hwp" as (Hclosure φinv) "Hwp".
  iExists (fun σ => (∃ _ : cfgG Σ, φinv _ σ ∗ source_inv [existT Ta ea] (σ1a))%I).
  iIntros (Hinv).
  assert (Inhabited Λa.(OpState)).
  { eexists; eauto. } (* econstructor. exact O. exact σ1a. } *)
  iMod (source_cfg_init [existT _ ea] (σ1a)) as (cfgG) "(#Hsrc&Hpool&HstateA)"; auto.
  { intros Herr; apply Hno_fault. apply exec_partial_err_exec_err; eauto. }
  iMod ("Hwp" $! _ _) as (stateI) "Hwand".
  iMod ("Hwand" with "[Hpool HstateA]") as "[Hstate [H [Hinv #Hφ]]]"; eauto.
  { iFrame. iFrame "#".
    rewrite /source_pool_map/tpool_to_map fmap_insert fmap_empty insert_empty //=.
  }
  iExists stateI. iIntros "{$Hstate} !>".
  iSplitL "H"; last iSplitL "Hinv".
  * iApply wp_wand_l; iFrame "H". iIntros (vc) "H".
    iDestruct "H" as (va) "(Hmapsto&Hopen)".
    iIntros (σ2c') "Hstate".
    iMod ("Hopen" with "Hstate") as (σ2a) "(Hstate&Habsr)".
    iInv "Hsrc" as (tp' n' σ') ">[Hauth Hp]" "_".
    iDestruct "Hp" as %Hp. destruct Hp as (Hp&Hno_fault'). rewrite //= in Hp.
    iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
    iDestruct (source_thread_reconcile with "Hmapsto Hauth") as %Hlookup; subst.
    apply take_drop_middle in Hlookup.

    iApply fupd_mask_weaken; first by set_solver+.
    iExists va, (n', σ'). iSplit; auto. iPureIntro. 
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
    iMod (inv_alloc sourceN ⊤ (source_inv _ _) with "HcfgInv") as "#cfgInv".
    iMod ("Hφ" with "[//] [$]") as (stateI') "(Hstate&Hwp&Hinv)".
    iModIntro. iExists stateI'. iFrame.
    iSplitL "Hwp".
    ** iApply wp_wand_l; iFrame.
       iIntros (_) "H1".
       iIntros (σ) "Hstate".
       iMod ("H1" with "[$]") as (σ2a σ3a) "(Hstate&Hp&Habsr)".
       iDestruct "Hp" as %Hcrash.
       iMod (inv_open_timeless with "cfgInv") as "(Hinv&_)"; first by eassumption.
       iApply fupd_mask_weaken; auto.
       { set_solver+. }
       iDestruct "Hinv" as (tp' n' σ3a') "(Hauth&%&%)".
       iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
       iExists _, _, (1, snd σ3a).

       iFrame. iPureIntro; intuition eauto.
       eapply crash_step_snd; eauto.
    ** iIntros. iMod ("Hinv" with "[$]").
       iMod (inv_open_timeless with "cfgInv") as "(?&_)"; first by eassumption.
       iApply fupd_mask_weaken; auto.
       { set_solver+. }
       iFrame. iExists _; iFrame.
Qed.

Theorem wp_recovery_refinement_adequacy_internal {Ta Tc R} OpTa OpTc Σ
        (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (ea: proc OpTa Ta) (ec: proc OpTc Tc) (rec: proc OpTc R) σ1a σ1c φ φrec E k
        (Hno_fault : ¬ exec Λa ea (1, σ1a) Err):
  wp_recovery_refinement Σ Λa Λc ea ec rec (1, σ1a) σ1c φ φrec E k ⊢
  recv_adequate_internal NotStuck ec rec σ1c
    (λ v σ2c, ∃ va σ2a, ⌜ exec Λa ea (1, σ1a) (Val σ2a (existT _ va)) ⌝
                            ∗ φ va v (snd σ2a) (snd σ2c))%I
    (λ σ2c, ∃ tp2 σ2a σ2a', ⌜ exec_partial Λa ea (1, σ1a) (Val σ2a tp2) ∧
                            lifted_crash_step Λa σ2a (Val σ2a' tt) ⌝ ∗ φrec (snd σ2a') (snd σ2c))%I k.
Proof.
  iIntros "Hwp".
  unshelve (iApply wp_recovery_adequacy_internal); eauto.
  iApply wp_recovery_refinement_impl_wp_recovery; eauto.
Qed.

Theorem wp_proc_seq_refinement_adequacy_internal {Ta Tc R} OpTa OpTc Σ (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (esa: proc_seq OpTa Ta) (esc: proc_seq OpTc Tc) (rec: proc OpTc R) σ1c σ1a
        φ P E k
        (Hno_fault : ¬ proc_exec_seq Λa esa (rec_singleton (Ret tt)) (1, σ1a) Err)
        (Hφ: ∀ va vc σ2a σ2c, φ va vc σ2c σ2a -∗ ⌜ P va vc ⌝):
  Nat.iter k (λ P, |==> ▷ P)%I (wp_proc_seq_refinement Λa Λc esa esc rec (1, σ1a) σ1c φ E) ⊢
  (∀ n σ2c vc, ⌜proc_exec_seq_n Λc esc rec n σ1c (Val σ2c vc)⌝ →
                (Nat.iter (S k + n) (λ P, |==> ▷ P)%I
                          (⌜ ∃ va σ2a, proc_exec_seq Λa esa (rec_singleton (Ret tt))
                                                       (1, σ1a) (Val σ2a va) ∧ P va vc ⌝
                                       : iProp Σ))%I).
Proof.
  iIntros "Hwp". iIntros (n σ2c res Hexec). iRevert "Hwp".
  iInduction esa as [] "IH" forall (k n esc σ1c σ1a Hno_fault Hexec); iIntros "Hwp".
  - destruct esc.
    * iApply (@bupd_iter_le _ k) => //=; try lia.
      iApply bupd_iter_mono; last eauto.
      iIntros "H". iDestruct (Hφ with "H") as %?.
      iPureIntro. destruct Hexec as (?&Hpure). inversion Hpure; subst.
      eexists _, (1, σ1a). split; eauto. econstructor.
    * iApply (@bupd_iter_le _ k) => //=; try lia.
      iApply bupd_iter_mono; last eauto. auto.
  - destruct esc.
    { simpl.
      iApply (@bupd_iter_le _ k) => //=; try lia.
      iApply bupd_iter_mono; last eauto. auto.
    }
    destruct Hexec as (n1&n2&Heq&(res0&σ1'&Hhd&Hrest)).
      destruct Hhd as [Hnorm|Hrecv].
      ** destruct Hnorm as (v&(?&?)&Hexec&Hfinish).
         destruct Hfinish as ([]&(?&?)&Hfinish&Hpure).
         destruct Hfinish as ([]&(?&?)&Hputs&Hfinish).
         inversion Hputs; subst.
         inversion Hpure; subst.
         destruct Hfinish; subst.
         replace ((S k + (5 + n1 + S n2)))%nat with ((S k + 5 + n1) + S n2)%nat by lia.
         rewrite /wp_proc_seq_refinement -/wp_proc_seq_refinement.
         rewrite Nat_iter_add.
         unshelve (iPoseProof (wp_recovery_refinement_adequacy_internal with "Hwp") as "Hwp"); eauto.
         { intros Herr. apply Hno_fault. do 3 left. eauto. }
         iDestruct "Hwp" as "(Hwp&_)".
         iApply (@bupd_iter_le _ (S k + (S (S n1)))%nat); first by lia.
         iApply bupd_iter_mono; last by iApply "Hwp".

         iIntros "H".
         iDestruct "H" as (v' Hp) "H". subst.
         iDestruct "H" as (va σ2a Hexeca) "H".
         unshelve (iDestruct ("H" $! _ _) as (σ2a' Hfinisha) "H"); [| eauto|]; [].
         inversion H1; subst.
         iMod ("IH" $! _ O n2 with "[] [] H") as "H".
         { iPureIntro. intros Herr.
           eapply Hno_fault. right.
           do 2 eexists; split; eauto.
           left.
           do 2 eexists; split; eauto.
           exists tt. eexists. split; eauto.
           eapply lifted_finish_step_intro'; eauto.
           econstructor.
         }
         { eauto. }
         iModIntro.
         iNext.
         iApply bupd_iter_mono; last by iApply "H".
         iIntros "H".
         iDestruct "H" as (va'' σ2a'') "(%&%)".
         iPureIntro. exists va'', σ2a''; split; auto.
         do 2 eexists; split; eauto.
         left. do 2 eexists; split; eauto.
         eexists tt, _. split; eauto.
         eapply lifted_finish_step_intro'; eauto.
         econstructor.
      ** destruct Hrecv as ([]&(?&?)&Hrexec&Hfinish).
         destruct Hfinish as ([]&(?&?)&Hputs&Hpure).
         inversion Hpure. subst.
         destruct Hputs as (Hput&Hpure'). inversion Hpure'. subst.
         inversion Hput; subst.
         replace ((S k + (5 + n1 + S n2)))%nat with ((S k + (5 + n1)) + S n2)%nat by lia.
         rewrite /wp_proc_seq_refinement -/wp_proc_seq_refinement.
         rewrite Nat_iter_add.
         unshelve (iPoseProof (wp_recovery_refinement_adequacy_internal with "Hwp") as "Hwp"); eauto.
         { intros Herr. apply Hno_fault. do 3 left. eauto. }
         iDestruct "Hwp" as "(_&Hwp&_)".
         iApply bupd_iter_mono; last by iApply "Hwp".

         iIntros "H".
         iDestruct "H" as (v' Hp) "H". subst.
         iDestruct "H" as (σ2a Hexeca) "H".
         replace (S n2) with (1 + n2)%nat by auto.
         iMod ("IH" $! _ O n2 with "[] [] H") as "H".
         { iPureIntro. intros Herr.
           eapply Hno_fault. right.
           do 2 eexists; split; eauto.
           right.
           do 2 eexists; split; eauto; last econstructor.
           eapply rexec_singleton_ret_intro; intuition eauto.
           eexists (_, _); split; eauto; last econstructor.
           destruct σ2a; econstructor; eauto.
         }
         { eauto. }
         iModIntro.
         iNext.
         iApply bupd_iter_mono; last by iApply "H".
         iIntros "H".
         iDestruct "H" as (va' σ2a') "(%&%)".
         iPureIntro. exists va', σ2a'; split; auto.
         do 2 eexists; split; eauto.
         right.
         econstructor; last econstructor.
         econstructor; last econstructor.
         eapply rexec_singleton_ret_intro; intuition eauto.
         eexists (_, _); split; eauto; last econstructor.
         destruct σ2a; econstructor; eauto.
Qed.

Theorem wp_proc_seq_refinement_impl_wp_proc_seq {Ta Tc R} OpTa OpTc Σ
        (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (esa: proc_seq OpTa Ta) (esc: proc_seq OpTc Tc) (rec: proc OpTc R) σ1c σ1a φ E
        (Hno_fault : ¬ proc_exec_seq Λa esa (rec_singleton (Ret tt)) (1, σ1a) Err):
  wp_proc_seq_refinement Λa Λc esa esc rec (1, σ1a) (1, σ1c) φ E ⊢
  wp_proc_seq NotStuck esc rec (1, σ1c)
    (λ (vc : Tc) (σ2c : State Λc), ∃ va σ2a, φ va vc σ2a (1, σ2c.2)).
Proof.
  revert esc σ1c σ1a Hno_fault.
  induction esa as [| ??? IH] => esc σ1c σ1a Hno_fault.
  - destruct esc; simpl; eauto. iIntros "[]".
  - destruct esc; first by (simpl; eauto; iIntros "[]").
    rewrite /wp_proc_seq_refinement -/wp_proc_seq_refinement.
    iIntros "Hwp".
    iPoseProof (wp_recovery_refinement_impl_wp_recovery with "Hwp") as "Hwp".
    { intros Hexec. apply Hno_fault. do 2 left. do 2 left.
      by apply exec_partial_err_exec_err. }
    iApply wp_recovery_mono; last iApply "Hwp"; rewrite -/wp_proc_seq.
    * iIntros (??) "H".
      iDestruct "H" as (va σ2a Hexeca) "H".
      iIntros.
      iDestruct ("H" $! _ Hfinish) as (σ2a' Hexeca') "H".
      simpl. iApply IH.
      { intros Herr. eapply Hno_fault. right. do 2 eexists; split; eauto.
        left.
        do 2 eexists; split; eauto.
        do 2 eexists. split; eauto; last econstructor.
        rewrite /lifted_finish_step.
        eexists tt, (1, snd σ2a); split.
        * destruct σ2a. split; eauto. econstructor.
        * econstructor; eauto.
      }
      eauto.
    * iAlways. iIntros (?) "H".
      iDestruct "H" as (tp2 σ2a σ2a' (Hexeca&Hcrash)) "H".
        destruct σ2a.
        destruct σ2a'.
      iIntros.
      simpl. iApply IH.
      { intros Herr. eapply Hno_fault. right.
        do 2 eexists; split; eauto.
        right.
        do 2 eexists. split.
        eapply rexec_singleton_ret_intro; eauto.
        do 2 eexists; split; eauto; last econstructor.
        econstructor.
        econstructor.
        eauto.
      }
      eauto.
Qed.

Theorem wp_proc_seq_refinement_impl_wp_proc_seq' {Ta Tc R} OpTa OpTc Σ
        (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (esa: proc_seq OpTa Ta) (esc: proc_seq OpTc Tc) (rec: proc OpTc R) σ1c σ1a φ E
        (Hno_fault : ¬ proc_exec_seq Λa esa (rec_singleton (Ret tt)) (1, σ1a) Err):
  wp_proc_seq_refinement Λa Λc esa esc rec (1, σ1a) (1, σ1c) φ E ⊢
  wp_proc_seq NotStuck esc rec (1, σ1c) (λ _ _, True).
Proof.
  iIntros "H".
  iPoseProof (wp_proc_seq_refinement_impl_wp_proc_seq with "H") as "H"; auto.
  iApply wp_proc_seq_mono; last by iApply "H".
  iAlways. auto.
Qed.

Import uPred.
(* TODO: this can be generalized a bit to only require exact equality at
   certain types *)
Theorem wp_proc_seq_refinement_adequacy {T R} OpTa OpTc Σ (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (esa: proc_seq OpTa T) (esc: proc_seq OpTc T) (rec: proc OpTc R) σ1c σ1a φ E
        (Hno_fault : ¬ proc_exec_seq Λa esa (rec_singleton (Ret tt)) (1, σ1a) Err)
        (Hφ: ∀ va vc σ2a σ2c, φ va vc σ2c σ2a -∗ ⌜ va = vc ⌝):
  wp_proc_seq_refinement Λa Λc esa esc rec  (1, σ1a) (1, σ1c) φ E →
  ∀ σ2c res, proc_exec_seq Λc esc (rec_singleton rec) (1, σ1c) (Val σ2c res) →
  ∃ σ2a, proc_exec_seq Λa esa (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
Proof.
  intros Hwp ?? Hexec.
  eapply proc_exec_seq_equiv_proc_exec_seq_n in Hexec as (n&?); last first.
  { eapply proc_seq_adequate_not_stuck; eauto.
    eapply wp_proc_seq_adequacy with (k := 0) (φ0 := λ _ _, True); eauto.
    simpl.
    iApply (wp_proc_seq_refinement_impl_wp_proc_seq' with "[]"); eauto.
    iApply Hwp.
  }
  { eauto using lifted_crash_non_err. }
  eapply (soundness (M:=iResUR Σ) _ (S O + n)).
  iApply bupd_iter_laterN_mono; first by reflexivity; eauto.
  iApply bupd_iter_mono; last first.
  {
    iApply (wp_proc_seq_refinement_adequacy_internal); eauto.
    iApply Hwp; eauto.
  }
  iIntros "H". iDestruct "H" as %(va&σ2a&Hexec&Heq).
  subst. eauto.
Qed.
