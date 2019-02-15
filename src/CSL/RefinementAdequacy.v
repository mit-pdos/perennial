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
Require Import Helpers.RelationAlgebra.

Definition wp_recovery_refinement {T R OpTa OpTc} Σ (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (ea: proc OpTa T) (ec: proc OpTc T) (rec: proc OpTc R) σ1a σ1c φ φrec E k :=
  Nat.iter k (λ P, |==> ▷ P)%I
    ((⌜ nclose sourceN ⊆ E ⌝ ∧
             ∃ (φinv : forall {_ : @cfgG OpTa Λa Σ}, Λc.(State) → iProp Σ),
         ∀ `{Hinv : invG Σ} `{Hcfg: cfgG OpTa Λa Σ},
          (|={⊤}=> ∃ stateI : State Λc → iProp Σ,
             let _ : irisG OpTc Λc Σ := IrisG _ _ _ Hinv stateI in
             (source_ctx ([existT _ ea], σ1a) ∗ O ⤇ ea ∗ source_state σ1a)
               ={⊤}=∗
               stateI σ1c
               ∗ WP ec @ NotStuck; ⊤ {{ v, O ⤇ of_val v
                    ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ ∃ σ2a, source_state σ2a ∗ φ v σ2a σ2c)}}
                    ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ φinv σ2c)
        ∗
        □ (∀ `{Hinv : invG Σ} `{Hcfg: cfgG OpTa Λa Σ} σ1c σ1c'
           (Hcrash: Λc.(crash_step) σ1c (Val σ1c' tt)),
            (φinv σ1c ={⊤}=∗ ∃ stateI : State Λc → iProp Σ,
               let _ : irisG OpTc Λc Σ := IrisG _ _ _ Hinv stateI in
               stateI σ1c'
               ∗ WP rec @ NotStuck; ⊤ {{ v, (∀ σ2c, stateI σ2c ={⊤,E}=∗
                   ∃ σ2a σ2a', source_state σ2a ∗ ⌜Λa.(crash_step) σ2a (Val σ2a' tt) ⌝ ∗
                               φrec σ2a' σ2c )}}
               ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ φinv σ2c))))))%I.

Fixpoint map_proc_seq {OpTa OpTc T} (f: ∀ T, proc OpTa T → proc OpTc T) (es: proc_seq OpTa T) :=
  match es with
  | Proc_Seq_Final e => Proc_Seq_Final (f _ e)
  | @Proc_Seq_Bind _ _ _  e es' =>
    Proc_Seq_Bind (f _ e) (fun x => map_proc_seq f (es' x))
  end.

Fixpoint wp_proc_seq_refinement {T R OpTa OpTc} {Σ} (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (es: proc_seq OpTa T) (rec: proc OpTc R) (f: ∀ T, proc OpTa T → proc OpTc T)
        σ1a σ1c φ φrec E : iProp Σ :=
  match es with
  | Proc_Seq_Final e => wp_recovery_refinement Σ Λa Λc e (f _ e) rec σ1a σ1c φ φrec E O
  | @Proc_Seq_Bind _ _ T0 e es' =>
    wp_recovery_refinement Σ Λa Λc e (f _ e) rec σ1a σ1c
      (λ v σ2a σ2c, wp_proc_seq_refinement Λa Λc (es' (Normal (existT T0 v)))
                                           rec f σ2a σ2c φ φrec E)%I
      (λ σ2a σ2c, wp_proc_seq_refinement Λa Λc (es' (Recovered (existT _ tt)))
                                         rec f σ2a σ2c φ φrec E) E O
  end.

Theorem wp_recovery_refinement_adequacy_internal {T R} OpTa OpTc Σ (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (ea: proc OpTa T) (ec: proc OpTc T) (rec: proc OpTc R) σ1a σ1c φ φrec E k
        (Hno_fault : ¬ exec Λa ea σ1a Err):
  wp_recovery_refinement Σ Λa Λc ea ec rec σ1a σ1c φ φrec E k ⊢
  recv_adequate_internal NotStuck ec rec σ1c
    (λ v σ2c, ∃ σ2a, ⌜ exec Λa ea σ1a (Val σ2a (existT _ v)) ⌝ ∗ φ v σ2a σ2c)%I
    (λ σ2c, ∃ tp2 σ2a σ2a', ⌜ exec_partial Λa ea σ1a (Val σ2a tp2) ∧
                            crash_step Λa σ2a (Val σ2a' tt) ⌝ ∗ φrec σ2a' σ2c)%I k.
Proof.
  iIntros "Hwp".
  unshelve (iApply wp_recovery_adequacy_internal); eauto.
  iApply (bupd_iter_mono with "[] Hwp"). iIntros "Hwp".
  iDestruct "Hwp" as (Hclosure φinv) "Hwp".
  iExists (fun σ => (∃ _ : cfgG Σ, φinv _ σ ∗ source_inv [existT T ea] σ1a)%I).
  iIntros (Hinv).
  assert (Inhabited Λa.(State)).
  { eexists; eauto. }
  iMod (source_cfg_init [existT _ ea] σ1a) as (cfgG) "(#Hsrc&Hpool&HstateA)"; auto.
  { intros Herr; apply Hno_fault. apply exec_partial_err_exec_err; eauto. }
  iMod ("Hwp" $! _ _) as (stateI) "Hwand".
  iMod ("Hwand" with "[Hpool HstateA]") as "[Hstate [H [Hinv #Hφ]]]"; eauto.
  { iFrame. iFrame "#".
    rewrite /source_pool_map/tpool_to_map fmap_insert fmap_empty insert_empty //=.
  }
  iExists stateI. iIntros "{$Hstate} !>".
  iSplitL "H"; last iSplitL "Hinv".
  * iApply wp_wand_l; iFrame "H". iIntros (v') "[Hmapsto Hopen]".
    iIntros (σ2c') "Hstate".
    iMod ("Hopen" with "Hstate") as (σ2a) "(Hstate&Habsr)".
    iInv "Hsrc" as (tp' σ') ">[Hauth Hp]" "_".
    iDestruct "Hp" as %Hp. destruct Hp as (Hp&Hno_fault'). rewrite //= in Hp.
    iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
    iDestruct (source_thread_reconcile with "Hmapsto Hauth") as %Hlookup; subst.
    apply take_drop_middle in Hlookup.

    iApply fupd_mask_weaken; first by set_solver+.
    iExists σ'. iSplit; auto. iPureIntro. 
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
       iMod ("H1" with "[$]") as (σ2a σ3a) "(Hstate&Hp&Habsr)".
       iDestruct "Hp" as %Hcrash.
       iMod (inv_open_timeless with "cfgInv") as "(Hinv&_)"; first by eassumption.
       iApply fupd_mask_weaken; auto.
       { set_solver+. }
       iDestruct "Hinv" as (tp' σ3a') "(Hauth&%&%)".
       iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
       iExists _, _, _. iFrame. iPureIntro; intuition eauto.
    ** iIntros. iMod ("Hinv" with "[$]").
       iMod (inv_open_timeless with "cfgInv") as "(?&_)"; first by eassumption.
       iApply fupd_mask_weaken; auto.
       { set_solver+. }
       iFrame. iExists _; iFrame.
Qed.

Theorem wp_proc_seq_refinement_adequacy_internal {T R} OpTa OpTc Σ (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (es: proc_seq OpTa T) (rec: proc OpTc R) f σ1c σ1a φ φrec E k
        (Hno_fault : ¬ Λa.(proc_exec_seq) es (rec_singleton (Ret tt)) σ1a Err):
  Nat.iter k (λ P, |==> ▷ P)%I (wp_proc_seq_refinement Λa Λc es rec f σ1a σ1c φ φrec E) ⊢
  (∀ n σ2c res, ⌜Λc.(proc_exec_seq_n) (map_proc_seq f es) rec n σ1c (Val σ2c res)⌝ →
                (Nat.iter (S k + n) (λ P, |==> ▷ P)%I
                          (⌜ ∃ σ2a, Λa.(proc_exec_seq) es (rec_singleton (Ret tt))
                                                       σ1a (Val σ2a res) ⌝ : iProp Σ))%I).
Proof.
  iIntros "Hwp". iIntros (n σ2c res Hexec). iRevert "Hwp".
  iInduction es as [] "IH" forall (k n σ1c σ1a Hno_fault Hexec); iIntros "Hwp".
  - destruct Hexec as (n1&?&Hexec). subst. destruct Hexec as [Hnorm|Hrecv].
      ** destruct Hnorm as (v&?&Hexec&Hpure). inversion Hpure; subst.
         unshelve (iPoseProof (wp_recovery_refinement_adequacy_internal with "Hwp") as "Hwp"); eauto.
         { intros Hexec'. apply Hno_fault. by do 2 left. }
         iDestruct "Hwp" as "(Hwp&_)".
         iApply (@bupd_iter_le _ (S k + (S (S n1)))%nat); first by lia.
         iApply bupd_iter_mono; last by iApply "Hwp".
         iIntros "H".
         iDestruct "H" as (v' Hp) "H". subst.
         iDestruct "H" as (σ2a Hexeca) "H".
         iPureIntro. eexists. left. do 2 eexists. intuition eauto. econstructor.
      ** destruct Hrecv as ([]&?&Hrexec&Hpure). inversion Hpure; subst.
         unshelve (iPoseProof (wp_recovery_refinement_adequacy_internal with "Hwp") as "Hwp"); eauto.
         { intros Hexec'. apply Hno_fault. by do 2 left. }
         iDestruct "Hwp" as "(_&(Hwp&_))".
         iApply (@bupd_iter_le _ (S k + ((5 + n1)))%nat); first by lia.
         iApply bupd_iter_mono; last by iApply "Hwp".
         iIntros "H".
         iDestruct "H" as (tp σ2a) "H". subst.
         iDestruct "H" as (σ2a' Hexeca) "H".
         iPureIntro. exists σ2a'.  right.
         exists tt, σ2a'; split; last econstructor.
         eapply rexec_singleton_ret_intro; intuition eauto.
  - destruct Hexec as (n1&n2&Heq&(res0&σ1'&Hhd&Hrest)).
      destruct Hhd as [Hnorm|Hrecv].
      ** destruct Hnorm as (v&?&Hexec&Hpure). inversion Hpure; subst.
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
         iDestruct "H" as (σ2a Hexeca) "H".
         replace (S n2) with (1 + n2)%nat by auto.
         iMod ("IH" $! _ O n2 with "[] [] H") as "H".
         { iPureIntro. intros Herr.
           eapply Hno_fault. right.
           do 2 eexists; split; eauto.
           left.
           do 2 eexists; split; eauto.
           econstructor.
         }
         { eauto. }
         iModIntro.
         iNext.
         iApply bupd_iter_mono; last by iApply "H".
         iIntros "H".
         iDestruct "H" as (σ2a') "%".
         iPureIntro. exists σ2a'.
         do 2 eexists; split; eauto.
         left. do 2 eexists; split; eauto. econstructor.
      ** destruct Hrecv as ([]&?&Hexec&Hpure). inversion Hpure; subst.
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
         }
         { eauto. }
         iModIntro.
         iNext.
         iApply bupd_iter_mono; last by iApply "H".
         iIntros "H".
         iDestruct "H" as (σ2a') "%".
         iPureIntro. exists σ2a'.
         do 2 eexists; split; eauto.
         right.
         econstructor; last econstructor.
         econstructor; last econstructor.
         eapply rexec_singleton_ret_intro; intuition eauto.
Qed.

Import uPred.
Theorem wp_proc_seq_refinement_adequacy {T R} OpTa OpTc Σ (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (es: proc_seq OpTa T) (rec: proc OpTc R) f σ1c σ1a φ φrec E
        (Hno_fault : ¬ Λa.(proc_exec_seq) es (rec_singleton (Ret tt)) σ1a Err):
  wp_proc_seq_refinement Λa Λc es rec f σ1a σ1c φ φrec E →
  ∀ σ2c res, Λc.(proc_exec_seq) (map_proc_seq f es) (rec_singleton rec) σ1c (Val σ2c res) →
  ∃ σ2a, Λa.(proc_exec_seq) es (rec_singleton (Ret tt)) σ1a (Val σ2a res).
Proof.
  intros Hwp ?? Hexec.
  eapply proc_exec_seq_equiv_proc_exec_seq_n in Hexec as (n&?); last first.
  { admit. (* just need to show non-error *) }
  { eauto using crash_non_err. }
  eapply (soundness (M:=iResUR Σ) _ (S O + n)).
  iApply bupd_iter_laterN_mono; first by reflexivity; eauto.
  iApply (wp_proc_seq_refinement_adequacy_internal); eauto.
  iApply Hwp; eauto.
Admitted.

(*
Theorem wp_recovery_crash_refinement {T R} OpTa OpTc Σ (Λa: Layer OpTa) (Λc: Layer OpTc)
        `{invPreG Σ} `{cfgPreG OpTa Λa Σ}
        (ea: proc OpTa T) (ec: proc OpTc T) (rec: proc OpTc R)
        (φinv : forall {_ : @cfgG OpTa Λa Σ}, Λc.(State) → iProp Σ)
        (absr: forall _ : @cfgG OpTa Λa Σ, Λa.(State) → Λc.(State) → iProp Σ) E:
  nclose sourceN ⊆ E →
  (∀ (σ1a: Λa.(State)) σ1c,
      (∀ `{Hinv : invG Σ} `{Hcfg: cfgG OpTa Λa Σ},
          (absr _ σ1a σ1c) -∗
          (|={⊤}=> ∃ stateI : State Λc → iProp Σ,
             let _ : irisG OpTc Λc Σ := IrisG _ _ _ Hinv stateI in
             (source_ctx ([existT _ ea], σ1a) ∗ O ⤇ ea ∗ source_state σ1a)
               ={⊤}=∗
               stateI σ1c
               ∗ WP ec @ NotStuck; ⊤ {{ v, O ⤇ of_val v
                    ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ ∃ σ2a, source_state σ2a ∗ absr _ σ2a σ2c)}}
                                     ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ φinv σ2c)
        ∗
        □ (∀ `{Hinv : invG Σ} `{Hcfg: cfgG OpTa Λa Σ} σ1c σ1c'
           (Hcrash: Λc.(crash_step) σ1c (Val σ1c' tt)),
            (φinv σ1c ={⊤}=∗ ∃ stateI : State Λc → iProp Σ,
               let _ : irisG OpTc Λc Σ := IrisG _ _ _ Hinv stateI in
               stateI σ1c'
               ∗ WP rec @ NotStuck; ⊤ {{ v, (∀ σ2c, stateI σ2c ={⊤,E}=∗
                   ∃ σ2a σ2a', source_state σ2a ∗ ⌜Λa.(crash_step) σ2a (Val σ2a' tt) ⌝ ∗
                               absr _ σ2a' σ2c)}}
                                     ∗ (∀ σ2c, stateI σ2c ={⊤,E}=∗ φinv σ2c)))))%I) →
  crash_refines (absr_to_iProp absr) Λc ec (rec_singleton rec) (Λa.(exec) ea)
                (and_then (Λa.(exec_halt) ea) (fun _ => Λa.(crash_step))).
Proof.
  intros Hsub Hwp.
  assert (Hno_fault_cut :
            ∀ σ1a, ¬ (v <- exec Λa ea; _ <- (absr_to_iProp absr); pure v) σ1a Err ->
                   ¬ exec Λa ea σ1a Err).
  { clear. intros σ1a Hno_err.
    intros Hexec. apply Hno_err.
    left; auto.
  }
  assert (Hno_fault_cut':
            ∀ σ1a, ¬ (v <- _ <- exec_halt Λa ea;
                          Λa.(crash_step); _ <- (absr_to_iProp absr); pure v) σ1a Err ->
                   ¬ exec Λa ea σ1a Err).
  { clear. intros σ1a Hno_err.
    intros Hexec. apply Hno_err. do 3 left. apply exec_partial_err_exec_err; eauto.
  }
  assert (Hadeq: ∀ σ1a σ1c (Hno_fault : ¬  exec Λa ea σ1a Err),
             (absr_to_iProp absr σ1a (Val σ1c tt)) →
             recv_adequate_internal (Σ := Σ) NotStuck ec rec σ1c
                          (λ v' σ2c', ∃ H σ2a, ⌜ exec Λa ea σ1a (Val σ2a (existT _ v')) ⌝ ∗
                                             absr H σ2a σ2c')%I
                          (λ σ2c', ∃ H tp2 σ2a σ3a, ⌜ exec_partial Λa ea σ1a (Val σ2a tp2) ∧
                                                      crash_step Λa σ2a (Val σ3a tt) ⌝ ∗
                                                   absr H σ3a σ2c')%I).
  { intros σ1a σ1c ? (k&Habsr_init).
    eapply wp_recovery_adequacy_internal with
        (φinv0 := fun σ => (∃ _ : cfgG Σ, φinv _ σ ∗ source_inv [existT T ea] σ1a)%I)
        (k0 := k); eauto.
    iIntros (Hinv).
    assert (Inhabited Λa.(State)).
    { eexists; eauto. }
    iPoseProof Habsr_init as "Habsr_init".
    iApply (bupd_iter_mono with "[] Habsr_init"). iClear "Habsr_init".
    iIntros "Habsr_init".
    iMod (source_cfg_init [existT _ ea] σ1a) as (cfgG) "(#Hsrc&Hpool&HstateA)"; auto.
    { intros Herr; apply Hno_fault. apply exec_partial_err_exec_err; eauto. }
    iPoseProof (Hwp _ _ with "Habsr_init") as "H".
    iMod "H" as (stateI) "Hwand"; eauto.
    iMod ("Hwand" with "[Hpool HstateA]") as "[Hstate [H [Hinv #Hφ]]]"; eauto.
    { iFrame. iFrame "#".
      rewrite /source_pool_map/tpool_to_map fmap_insert fmap_empty insert_empty //=.
    }
    iExists stateI. iIntros "{$Hstate} !>".
    iSplitL "H"; last iSplitL "Hinv".
    * iApply wp_wand_l; iFrame "H". iIntros (v') "[Hmapsto Hopen]".
      iIntros (σ2c') "Hstate".
      iMod ("Hopen" with "Hstate") as (σ2a) "(Hstate&Habsr)".
      iInv "Hsrc" as (tp' σ') ">[Hauth Hp]" "_".
      iDestruct "Hp" as %Hp. destruct Hp as (Hp&Hno_fault'). rewrite //= in Hp.
      iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
      iDestruct (source_thread_reconcile with "Hmapsto Hauth") as %Hlookup; subst.
      apply take_drop_middle in Hlookup.

      iApply fupd_mask_weaken; first by set_solver+.
      iExists _, σ'. iSplit; auto. iPureIntro. 
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
         iMod ("H1" with "[$]") as (σ2a σ3a) "(Hstate&Hp&Habsr)".
         iDestruct "Hp" as %Hcrash.
         iMod (inv_open_timeless with "cfgInv") as "(Hinv&_)"; first by eassumption.
         iApply fupd_mask_weaken; auto.
         { set_solver+. }
         iDestruct "Hinv" as (tp' σ3a') "(Hauth&%&%)".
         iDestruct (source_state_reconcile with "Hstate Hauth") as %Hstate; subst.
         iExists _, _, _, _. iFrame. iPureIntro; intuition eauto.
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
      edestruct Hadeq; eauto.
      eapply recv_adequate_internal_not_stuck; eauto.
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
*)