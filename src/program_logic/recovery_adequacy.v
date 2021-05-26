From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang recovery_weakestpre.
From Perennial.program_logic Require Import crash_adequacy.
Import uPred.

Set Default Proof Using "Type".

Section recovery_adequacy.
Context `{!perennialG Λ CS T Σ}.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φinv : crashG Σ → pbundleG T Σ → iProp Σ.
Implicit Types Φc : crashG Σ → pbundleG T Σ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Notation wptp s k t := ([∗ list] ef ∈ t, WPC ef @ s; k; ⊤ {{ fork_post }} {{ True }})%I.

Notation steps_sum := crash_adequacy.steps_sum.

Fixpoint step_fupdN_fresh ncurrent (ns: list nat) (Hc0: crashG Σ) t0
         (P: crashG Σ → pbundleG T Σ → iProp Σ) {struct ns} :=
  match ns with
  | [] => P Hc0 t0
  | (n :: ns) =>
    (||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum (perennial_num_laters_per_step) (perennial_step_count_next)
                                     ncurrent (S n)) ||={∅|∅, ⊤|⊤}=>
     ||={⊤|⊤,∅|∅}=> ||▷=>^2 ||={∅|∅, ⊤|⊤}=>
     ∀ Hc', NC 1 ={⊤}=∗ (∃ t' : pbundleG T Σ, step_fupdN_fresh ((Nat.iter (S n) step_count_next ncurrent)) ns Hc' t' P))%I
  end.

Lemma step_fupdN_fresh_pattern_fupd {H: invGS Σ} n k (Q Q': iProp Σ):
  (||={⊤|⊤,∅|∅}=> ||▷=>^n ||={∅|∅, ⊤|⊤}=> ||={⊤|⊤,∅|∅}=> ||▷=>^k ||={∅|∅, ⊤|⊤}=> Q) -∗ (Q -∗ ||={⊤|⊤, ⊤|⊤}=> Q') -∗
  (||={⊤|⊤,∅|∅}=> ||▷=>^n ||={∅|∅, ⊤|⊤}=> ||={⊤|⊤,∅|∅}=> ||▷=>^k ||={∅|∅, ⊤|⊤}=> Q').
Proof.
  iIntros "H Hwand". simpl.
  iApply (step_fupd2N_wand with "H").
  iIntros "H".
  iMod "H". iModIntro.
  iMod "H". iModIntro.
  iApply (step_fupd2N_wand with "H").
  iIntros "H".
  iMod "H". by iApply "Hwand".
Qed.

(*
Lemma step_fupdN_fresh_pattern_bupd {H: invGS Σ} n (Q Q': iProp Σ):
  (|={⊤,⊤}_n=> |={⊤,⊤}_2=> Q) -∗ (Q ==∗ Q') -∗
  (|={⊤,⊤}_n=> |={⊤,⊤}_2=> Q').
Proof.
  iIntros "H Hwand". iApply (step_fupdN_fresh_pattern_fupd with "H").
  iIntros. by iMod ("Hwand" with "[$]").
Qed.

Lemma step_fupdN_fresh_pattern_wand {H: invGS Σ} n (Q Q': iProp Σ):
  (|={⊤,⊤}_n=> |={⊤,⊤}_2=> Q) -∗ (Q -∗ Q') -∗
  (|={⊤,⊤}_n=> |={⊤,⊤}_2=> Q').
Proof.
  iIntros "H Hwand". iApply (step_fupdN_fresh_pattern_bupd with "H").
  iIntros. by iApply "Hwand".
Qed.
*)

Lemma step_fupdN_fresh_pattern_plain {H: invGS Σ} n (Q: iProp Σ) `{!Plain Q}:
  (||={⊤|⊤,∅|∅}=> ||▷=>^n ||={∅|∅, ⊤|⊤}=> ||={⊤|⊤,∅|∅}=> ▷ Q) -∗
  (||={⊤|⊤,⊤|⊤}=> ▷^(S n) Q).
Proof.
  iIntros "H".
  iApply fupd2_plain_mask_empty.
  destruct n.
  { iMod "H". simpl. iMod "H". eauto. }
  iMod "H".
  iAssert (||▷=>^(S n) ||={∅|∅, ∅|∅}=> ▷ Q)%I with "[H]" as "H".
  { rewrite ?Nat_iter_S_r. iApply (step_fupd2N_wand with "H").
    iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iMod "H". iMod "H".
    iModIntro. eauto. }
  iDestruct (step_fupd2N_plain with "H") as "H".
  iMod "H". iModIntro. iNext. rewrite -later_laterN laterN_later. iNext. by iMod "H".
Qed.

Lemma step_fupdN_fresh_pattern_plain' {H: invGS Σ} n (Q: iProp Σ) `{!Plain Q}:
  (||={⊤|⊤,∅|∅}=> ||▷=>^n ||={∅|∅, ⊤|⊤}=> ||={⊤|⊤,∅|∅}=> ||▷=>^2 ||={∅|∅, ∅|∅}=> ▷ Q) -∗
  (||={⊤|⊤, ⊤|⊤}=> ▷^(S (S (S (S n)))) Q).
Proof.
  iIntros "H".
  iApply step_fupdN_fresh_pattern_plain.
  replace (S (S (S n))) with (n + 3) by lia.
  iApply step_fupd2N_inner_plus.
  iApply (step_fupd2N_inner_wand with "H"); auto.
  iIntros "H".
  iAssert (||={⊤|⊤,∅|∅}=> ▷^3 ◇ Q)%I with "[H]" as "H".
  iMod "H".
  iPoseProof (step_fupd2N_plain with "H") as "H".
  iMod "H". iModIntro. iNext. iNext. iMod "H". eauto.
  iMod (fupd2_plain_mask with "H") as "H". eauto.
  iApply step_fupd2N_inner_later; auto. iNext. iNext. iNext.
  iMod (fupd2_mask_subseteq ∅ ∅); auto. iModIntro. iMod "H". eauto.
Qed.

Lemma step_fupdN_fresh_wand ncurr1 ncurr2 (ns: list nat) Hc0 t0 Q Q':
  ncurr1 = ncurr2 →
  step_fupdN_fresh ncurr1 (ns) Hc0 t0 Q -∗ (∀ Hc t, Q Hc t -∗ Q' Hc t)
  -∗ step_fupdN_fresh ncurr2 ns Hc0 t0 Q'.
Proof.
  revert Hc0 t0 ncurr1 ncurr2.
  induction ns => ?????.
  - iIntros "H Hwand". iApply "Hwand". eauto.
  - iIntros "H Hwand". rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    iApply (step_fupd2N_inner_wand with "H"); try auto.
    { subst. auto. }
    iIntros "H".
    iMod "H". iModIntro. iApply (step_fupd2N_wand with "H"). iIntros "H".
    iMod "H". iModIntro.
    iIntros (Hc') "HNC". iSpecialize ("H" $! Hc' with "[$]"). iMod "H" as (?) "H".
    iExists _. iModIntro. iApply (IHns with "H").
    { subst. auto. }
    eauto.
Qed.

Lemma wptp_recv_strong_normal_adequacy Φ Φinv Φr κs' s k Hc t n ns ncurr mj D r1 e1 t1 κs t2 σ1 g1 σ2 g2 :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) Normal →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ncurr mj D (κs ++ κs') -∗
  wpr s k Hc t ⊤ e1 r1 Φ Φinv Φr -∗
  wptp s k t1 -∗ NC 1-∗ step_fupdN_fresh ncurr ns Hc t (λ Hc' t',
    ⌜ Hc' = Hc ∧ t' = t ⌝ ∗
    (||={⊤|⊤,∅|∅}=> ||▷=>^(steps_sum num_laters_per_step step_count_next ncurr n) ||={∅|∅,⊤|⊤}=>
    ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ▷^(S (S (num_laters_per_step (Nat.iter n step_count_next ncurr))))
        (⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 g2 ⌝) ∗
    state_interp σ2 (length t2') ∗
    global_state_interp g2 (Nat.iter n step_count_next ncurr) mj D κs' ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1)).
Proof.
  iIntros (Hstep) "Hσ Hg He Ht HNC".
  inversion Hstep. subst.
  iPoseProof (wptp_strong_adequacy with "Hσ Hg [He] Ht") as "H".
  { eauto. }
  {rewrite wpr_unfold /wpr_pre. iApply "He". }
  rewrite perennial_crashG.
  iSpecialize ("H" with "[$]").
  assert (ns = []) as ->;
    first by (eapply nrsteps_normal_empty_prefix; eauto).
  inversion H. subst.
  rewrite /step_fupdN_fresh.
  iSplitL ""; first by eauto.
  iApply (step_fupd2N_wand with "H"); auto.
Qed.

Fixpoint sum_crash_steps ns :=
  match ns with
  | [] => 0
  | n :: ns => (S n) + (sum_crash_steps ns)
  end.

Lemma wptp_recv_strong_crash_adequacy Φ Φinv Φinv' Φr κs' s k Hc t ncurr mj D ns n r1 e1 t1 κs t2 σ1 g1 σ2 g2 :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) Crashed →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ncurr mj D (κs ++ κs') -∗
  wpr s k Hc t ⊤ e1 r1 Φ Φinv Φr -∗
  □ (∀ Hc' t', Φinv Hc' t' -∗ □ Φinv' Hc' t') -∗
  wptp s k t1 -∗ NC 1-∗ step_fupdN_fresh ncurr ns Hc t (λ Hc' t',
    let ntot := (steps_sum perennial_num_laters_per_step perennial_step_count_next
                           (Nat.iter (sum_crash_steps ns) perennial_step_count_next ncurr )
                           n)  in
    let ntot' := ((Nat.iter (n + sum_crash_steps ns) perennial_step_count_next ncurr)) in
    (||={⊤|⊤, ∅|∅}=> ||▷=>^ntot ||={∅|∅, ⊤|⊤}=> (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ▷^(S (S (num_laters_per_step $ ntot'))) (⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 g2⌝) ∗
    state_interp σ2 (length t2') ∗
    global_state_interp g2 ntot' mj D κs' ∗
    from_option (Φr Hc' t') True (to_val e2) ∗
    □ Φinv' Hc' t' ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1))).
Proof.
  revert Hc t e1 t1 κs κs' t2 σ1 g1 ncurr σ2 Φ.
  induction ns as [|n' ns' IH] => Hc t e1 t1 κs κs' t2 σ1 g1 ncurr σ2 Φ.
  { rewrite app_nil_l.
    inversion 1.
    match goal with
    | [ H : nrsteps _ _ _ _ _ _ |- _ ] => inversion H
    end.
  }
  iIntros (Hsteps) "Hσ Hg He #Hinv Ht HNC".
  inversion_clear Hsteps as [|?? [t1' ?] ????? s0].
  rewrite {1}/step_fupdN_fresh -/step_fupdN_fresh.
  destruct ρ2 as (?&[σ2_pre_crash g2_pre_crash]).
  rewrite -assoc wpr_unfold /wpr_pre.
  rewrite Nat_iter_S.
  iPoseProof (@wptp_strong_crash_adequacy with "[$] [$] [$] [$]") as "H"; eauto.
  rewrite perennial_crashG.
  iSpecialize ("H" with "[$]").
  rewrite perennial_num_laters_per_step_spec.
  rewrite perennial_step_count_next_spec.
  iMod "H". iModIntro.
  iApply (step_fupd2N_wand (steps_sum perennial_num_laters_per_step perennial_step_count_next ncurr (S n'))
            with "H").
  iIntros "H".
  iMod "H".
  iModIntro. iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; try set_solver+.
  iModIntro. iModIntro. iNext.
  iMod ("Hclo") as "_".
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; try set_solver+.
  iMod ("Hclo") as "_".
  iDestruct "H" as (e2 t2' ?) "(H&Hσ&Hg&HC)".
  iMod ("H" with "[//] Hσ Hg") as "H".
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; try set_solver+. do 2 iModIntro. iNext.
  iModIntro.
  iMod ("Hclo") as "_".
  iModIntro.
  destruct s0.
  - iIntros (Hc') "HNC". iSpecialize ("H" $! Hc' with "[$]").
    iMod "H" as (t' Heqpf') "(Heq&Hσ&Hg&Hr&HNC)".
    iDestruct "Hr" as "(_&Hr)".
    simpl in *.
    iPoseProof (IH with "[Hσ] [Hg] Hr [] [] HNC") as "H"; eauto.
    iExists _. iModIntro. simpl. eauto.
    iApply (step_fupdN_fresh_wand with "H").
    { rewrite perennial_step_count_next_spec. auto. }
    iIntros (??) "H".
    iMod "H". iModIntro.
    rewrite {1}plus_comm Nat_iter_add.
    rewrite -Nat_iter_S Nat_iter_S_r.
    rewrite perennial_step_count_next_spec.
    iApply step_fupd2N_le; last iApply (step_fupd2N_wand with "H").
    { apply Nat.eq_le_incl. f_equal.
      rewrite {1}plus_comm ?Nat_iter_add.
      f_equal. rewrite -Nat_iter_S -Nat_iter_S_r //. }
    iIntros ">H".
    rewrite {1}plus_comm ?Nat_iter_add.
    iDestruct "H" as (?? Heq) "(H1&?&Hg&?&?)".
    iExists _, _. iFrame "∗".
    iSplitL ""; first eauto.
    iSplitL "H1".
    { iModIntro. iNext. iNext. iApply (laterN_le with "H1"); auto.
      apply Nat.eq_le_incl. f_equal.
      rewrite -?Nat_iter_S_r -?Nat_iter_add plus_assoc.
      f_equal. lia. }
    iMod (global_state_interp_le with "Hg") as "$".
    { apply Nat.eq_le_incl.
      rewrite -?Nat_iter_S_r -?Nat_iter_add plus_assoc.
      f_equal. lia. }
    iModIntro; done.
  - iIntros (Hc') "HNC".
    iMod ("H" $! Hc' with "[$]") as (t' Heqpf') "(Heq&Hσ&Hg&Hr&HNC)".
    iExists t'.
    iAssert (□Φinv' Hc' t')%I as "#Hinv'".
    { iDestruct "Hr" as "(Hr&_)".
      iApply "Hinv". eauto.
    }
    iDestruct "Hr" as "(_&Hr)".
    iDestruct (wptp_recv_strong_normal_adequacy with "[Hσ] [Hg] [Hr] [] HNC") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H").
    { simpl. rewrite perennial_step_count_next_spec. lia. }
    iModIntro.
    iIntros (??) "H".
    iDestruct "H" as ((?&?)) "H". subst.
    iClear "HC". simpl.
    assert (ns' = []) as ->; first by (eapply nrsteps_normal_empty_prefix; eauto).
    simpl.
    rewrite ?perennial_num_laters_per_step_spec.
    rewrite ?perennial_step_count_next_spec.
    iApply (step_fupd2N_inner_wand with "H"); try set_solver+.
    { rewrite plus_0_r. auto. }
    iIntros "H".
    iFrame "Hinv'". rewrite Nat.add_0_r.
    rewrite -Nat_iter_S Nat_iter_S_r.
    rewrite Nat_iter_add Nat_iter_S_r.
    eauto.
Qed.

Lemma wptp_recv_strong_adequacy Φ Φinv Φinv' Φr κs' s k Hc t ns mj D n r1 e1 t1 κs t2 σ1 g1 ncurr σ2 g2 stat :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) stat →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ncurr mj D (κs ++ κs') -∗
  wpr s k Hc t ⊤ e1 r1 Φ Φinv Φr -∗
  □ (∀ Hc' t', Φinv Hc' t' -∗ □ Φinv' Hc' t') -∗
  wptp s k t1 -∗ NC 1-∗ step_fupdN_fresh ncurr ns Hc t (λ Hc' t',
    let ntot := (steps_sum perennial_num_laters_per_step perennial_step_count_next
                           (Nat.iter (sum_crash_steps ns) perennial_step_count_next ncurr )
                           n)  in
    let ntot' := ((Nat.iter (n + sum_crash_steps ns) perennial_step_count_next ncurr)) in
    (||={⊤|⊤, ∅|∅}=> ||▷=>^ntot ||={∅|∅, ⊤|⊤}=> (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ▷^(S (S (num_laters_per_step $ ntot'))) (⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 g2 ⌝) ∗
    state_interp σ2 (length t2') ∗
    global_state_interp g2 ntot' mj D κs' ∗
    (match stat with
     | Normal => ⌜ Hc' = Hc ∧ t' = t ⌝ ∗ from_option Φ True (to_val e2)
     | Crashed => from_option (Φr Hc' t') True (to_val e2) ∗ □ Φinv' Hc' t'
     end)  ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1))).
Proof.
  intros. destruct stat.
  - iIntros. iDestruct (wptp_recv_strong_crash_adequacy with "[$] [$] [$] [$] [$] [$]") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H"); first auto.
    iIntros (??) "H".
    iApply (step_fupd2N_wand with "H"); auto.
    iIntros "H".
    iMod "H" as (???) "(?&H&?&?&?)". iExists _, _.
    repeat (iSplitL ""; try iFrame; eauto).
  - iIntros. iDestruct (wptp_recv_strong_normal_adequacy with "[$] [$] [$] [$] [$]") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H"); first auto.
    iIntros (??) "H".
    iDestruct "H" as ((?&?)) "H". subst.
    assert (ns = []) as ->; first by (eapply nrsteps_normal_empty_prefix; eauto).
    simpl. rewrite Nat.add_0_r.
    iMod "H". iModIntro.
    rewrite perennial_num_laters_per_step_spec.
    rewrite perennial_step_count_next_spec.
    iApply (step_fupd2N_wand with "H"); auto.
    iIntros "H".
    iMod "H" as (???) "(?&H&?&?&?)". iExists _, _.
    iSplitL ""; first eauto. iFrame. eauto.
Qed.

End recovery_adequacy.

Fixpoint fresh_later_count f g ncurr (ns: list nat) :=
  match ns with
  | [] => 0
  | n :: ns' => S (S (S (crash_adequacy.steps_sum f g ncurr (S n))))
                 + fresh_later_count f g (Nat.iter (S n) g ncurr) ns'
  end.


Lemma step_fupdN_fresh_plain {Λ CS T Σ} `{!invGpreS Σ} `{!crashPreG Σ} P `{!Plain P} ns ncurr f g k:
  (∀ (Hi': invGS Σ) Hc', NC 1-∗ |={⊤}=>
   ∃ (pG: perennialG Λ CS T Σ)
     (Hpf1: ∀ Hc t, @iris_invG _ _ (perennial_irisG Hc t) = Hi')
     (Hpf2: perennial_num_laters_per_step = f)
     (Hpf3: perennial_step_count_next = g) t,
     |={⊤}=> step_fupdN_fresh ncurr ns Hc' t
                  (λ _ _, ||={⊤|⊤,∅|∅}=> ||▷=>^k ||={∅|∅, ⊤|⊤}=> P)) -∗
  ▷^(fresh_later_count f g ncurr ns + S k) P.
Proof.
  iIntros "H".
  iMod wsat_alloc' as (Hinv) "(Hw&HE)".
  iSpecialize ("H" $! Hinv).
  rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
  iApply (bupd_plain (▷^(_) P)%I); try (iPureIntro; apply _).
  iMod NC_alloc as (Hc) "HNC".
  iDestruct (ownE_weaken _ (AlwaysEn ∪ MaybeEn1 ⊤ ∪ MaybeEn2 ⊤) with "HE") as "HE"; first by set_solver.
  iDestruct (ownE_op with "HE") as "(HE&HE2)".
  { apply disjoint_union_l; split.
    - apply coPset_inl_inr_disj.
    - apply MaybeEn12_disj. }
  rewrite plus_comm. iEval (simpl).
  iMod ("H" with "[$] [$]") as "[>Hw [>HE >H]]"; eauto.
  iDestruct "H" as (pG Hpf1 Hpf2 Hpf3 t) "H".
  rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
  iMod ("H" with "[$]") as "[>Hw [>HE >H]]"; eauto.

  (* Have to strengthen the induction hypothesis to not lose wsat and ownE *)
  iAssert (||={⊤|⊤, ⊤|⊤}=> ▷ ▷^(k + fresh_later_count f g ncurr ns) P)%I with "[H]" as "Hgoal"; last first.
  {
    rewrite {1}uPred_fupd2_eq {1}/uPred_fupd2_def.
    iCombine "HE HE2" as "HE".
    rewrite -ownE_op; last first.
    { apply disjoint_union_l; split.
    - apply coPset_inl_inr_disj.
    - apply MaybeEn12_disj. }
    iMod ("Hgoal" with "[$]") as "[Hw [HE >H]]"; eauto.
  }

  iInduction ns as [| n' ns] "IH" forall (t Hc ncurr).
  - rewrite /step_fupdN_fresh.
    iApply step_fupd2N_inner_plain.
    iMod "H". iModIntro. simpl.
    rewrite Nat_iter_add. iApply (step_fupd2N_wand with "H").
    iIntros "H".
    iApply step_fupd2N_later; auto.
  - iMod NC_alloc as (Hc') "HNC".
    rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    iDestruct (step_fupdN_fresh_pattern_fupd _ _ _ (▷^ (S _) P)%I with "H [IH HNC]") as "H".
    { iIntros "H".
      iSpecialize ("H" with "[$]").
      rewrite ?Hpf1.
      rewrite ?Hpf2.
      rewrite ?Hpf3.
      iMod "H". iDestruct "H" as (t') "H".
      iMod ("IH" with "H") as "H".
      rewrite ?perennial_step_count_next_spec.
      iModIntro; eauto.
    }
    rewrite step_fupd2N_inner_plus.
    iPoseProof (step_fupd2N_inner_plain with "H") as "H".
    simpl.
    rewrite ?Hpf1.
    rewrite ?Hpf2.
    rewrite ?Hpf3.
    iMod "H". iModIntro.
    rewrite -?laterN_later.
    rewrite -?laterN_plus.
    iNext.
    rewrite -later_laterN.
    iApply (laterN_le with "H").
    { lia. }
Qed.

Lemma step_fupdN_fresh_soundness {Λ CS T Σ} `{!invGpreS Σ} `{!crashPreG Σ} (φ : Prop) ns ncurr k k2 f g:
  (∀ (Hi: invGS Σ) (Hc: crashG Σ), NC 1 ={⊤}=∗
    ∃ (pG: perennialG Λ CS T Σ) (Hpf1: ∀ Hc t, @iris_invG _ _ (perennial_irisG Hc t) = Hi)
     (Hpf2: perennial_num_laters_per_step = f) (Hpf2: perennial_step_count_next = g) t0,
      (|={⊤}=> step_fupdN_fresh ncurr ns Hc t0 (λ _ _,
       ||={⊤|⊤,∅|∅}=> ||▷=>^k ||={∅|∅, ⊤|⊤}=> ▷^k2 ⌜φ⌝))%I) →
  φ.
Proof.
  intros Hiter.
  eapply (soundness (M:=iResUR Σ) _  (_ + k2)); simpl.
  rewrite laterN_plus.
  iApply (step_fupdN_fresh_plain). iIntros (Hinv Hc).
  iIntros "H". by iApply Hiter.
Qed.

Record recv_adequate {Λ CS} (s : stuckness) (e1 r1: expr Λ) (σ1 : state Λ) (g1 : global_state Λ)
    (φ φr: val Λ → state Λ → global_state Λ → Prop) (φinv: state Λ → global_state Λ → Prop)  := {
  recv_adequate_result_normal t2 σ2 g2 v2 :
   erased_rsteps (CS := CS) r1 ([e1], (σ1,g1)) (of_val v2 :: t2, (σ2,g2)) Normal →
   φ v2 σ2 g2;
  recv_adequate_result_crashed t2 σ2 g2 v2 :
   erased_rsteps (CS := CS) r1 ([e1], (σ1,g1)) (of_val v2 :: t2, (σ2,g2)) Crashed →
   φr v2 σ2 g2;
  recv_adequate_not_stuck t2 σ2 g2 e2 stat :
   s = NotStuck →
   erased_rsteps (CS := CS) r1 ([e1], (σ1,g1)) (t2, (σ2,g2)) stat →
   e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2 g2);
  recv_adequate_inv t2 σ2 g2 stat :
   erased_rsteps (CS := CS) r1 ([e1], (σ1,g1)) (t2, (σ2,g2)) stat →
   φinv σ2 g2
}.

Lemma recv_adequate_alt {Λ CS} s e1 r1 σ1 g1 (φ φr : val Λ → state Λ → global_state Λ → Prop) φinv :
  recv_adequate (CS := CS) s e1 r1 σ1 g1 φ φr φinv ↔ ∀ t2 σ2 g2 stat,
    erased_rsteps (CS := CS) r1 ([e1], (σ1,g1)) (t2, (σ2,g2)) stat →
      (∀ v2 t2', t2 = of_val v2 :: t2' →
                 match stat with
                   | Normal => φ v2 σ2 g2
                   | Crashed => φr v2 σ2 g2
                 end) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2 g2)) ∧
      (φinv σ2 g2).
Proof.
  split.
  - intros [] ??? []; naive_solver.
  - constructor; naive_solver.
Qed.

Corollary wp_recv_adequacy_inv Σ Λ CS (T: ofe) `{!invGpreS Σ} `{!crashPreG Σ} nsinit s k e r σ g φ φr φinv f1 f2:
  (∀ `{Hinv : !invGS Σ} `{Hc: !crashG Σ} κs,
     ⊢ |={⊤}=> ∃ (t: pbundleG T Σ)
         (stateI : pbundleG T Σ → state Λ → nat → iProp Σ)
         (global_stateI : pbundleG T Σ → global_state Λ → nat → fracR → coPset → list (observation Λ) → iProp Σ)
         (fork_post : pbundleG T Σ → val Λ → iProp Σ) Hpf1a Hpf1b Hpf1' Hpf2 Hpf3 Hpf4
         Φinv,
        let _ : perennialG Λ CS _ Σ :=
            PerennialG _ _ T Σ
              (λ Hc t,
               IrisG Λ Σ Hinv Hc (stateI t) (global_stateI t) (fork_post t) f1 f2 (Hpf1a Hc t) Hpf1b) Hpf1' Hpf2 f1 Hpf3 f2 Hpf4
               in
       □ (∀ σ nt, stateI t σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
       □ (∀ Hc t', Φinv t Hinv Hc t' -∗ □ ∀ σ nt, stateI t' σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
       stateI t σ 0 ∗ global_stateI t g nsinit 1%Qp ∅ κs ∗
       wpr s k Hc t ⊤ e r (λ v, ⌜φ v⌝) (Φinv t Hinv) (λ _ _ v, ⌜φr v⌝)) →
  recv_adequate (CS := CS) s e r σ g (λ v _ _, φ v) (λ v _ _, φr v) (λ σ _, φinv σ).
Proof.
  intros Hwp.
  apply recv_adequate_alt.
  intros t2 σ2 g2 stat [n [κs H]]%erased_rsteps_nrsteps.
  destruct (nrsteps_snoc _ _ _ _ _ _ H) as (ns'&n'&->).
  eapply (step_fupdN_fresh_soundness _ ns' nsinit
              (crash_adequacy.steps_sum f1 f2 (Nat.iter (sum_crash_steps ns') f2 nsinit) n')
               (S (S  (f1 (Nat.iter (n' + sum_crash_steps ns') f2 nsinit)))))
         => Hinv Hc.
  iIntros "HNC".
  iMod (Hwp Hinv Hc κs) as (t stateI global_stateI Hfork_post Hpf1a Hpf1b Hpf1') "H".
  iDestruct "H" as (Hpf2 Hpf3 Hpf4) "H".
  iDestruct "H" as (Φinv) "(#Hinv1&#Hinv2&Hσ&Hg&H)".
  iModIntro.
  set (pG :=
          PerennialG _ _ T Σ
            (λ Hc t, IrisG Λ Σ Hinv Hc (stateI t) (global_stateI t) (Hfork_post t) f1 f2 (Hpf1a Hc t) Hpf1b) Hpf1'
            Hpf2 f1 Hpf3 f2 Hpf4).
  iExists pG.
  iDestruct (wptp_recv_strong_adequacy
                _ _ (λ Hc t, (∀ σ nt, stateI t σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝))%I
               _ [] with "[Hσ] [Hg] [H] [] [] HNC") as "H"; eauto.
  { rewrite app_nil_r. eauto. }
  iExists _.
  unshelve (iExists _); first by (rewrite //=).
  unshelve (iExists _); first by (rewrite //=).
  iExists t.
  iModIntro.
  iApply (step_fupdN_fresh_wand with "H").
  { auto. }
  iIntros (??) "H".
  iMod "H".
  rewrite /perennial_num_laters_per_step.
  iApply (step_fupd2N_wand with "H"); auto.
  iModIntro. iIntros "H".
  iMod "H" as (v2 ??) "(Hnstuck&Hσ&Hg&Hv&Hfpost&HNC)".
  destruct stat.
  - iDestruct "Hv" as "(Hv&#Hinv)".
    rewrite ?ncfupd_eq /ncfupd_def.
    iApply fupd2_plain_mask.
    iMod ("Hinv" with "[$] [$]") as "(Hp&HNC)".
    iDestruct "Hp" as %?. iModIntro.
    rewrite Hpf3.
    iNext. iNext.
    rewrite /perennial_step_count_next//=.
    iNext.
    iSplit; [| iSplit]; eauto.
    iIntros (v2' ? Heq). subst. inversion Heq; subst.
    rewrite to_of_val. naive_solver.
  - iDestruct "Hv" as "(Heq1&Hv)".
    iDestruct "Heq1" as %(?&?); subst.
    iApply fupd2_plain_mask.
    rewrite ?ncfupd_eq /ncfupd_def.
    iMod ("Hinv1" with "[$] [$]") as "(Hp&HNC)".
    iDestruct "Hp" as %?. iModIntro.
    iModIntro.
    rewrite Hpf3. iNext. iNext.
    iSplit; [| iSplit]; eauto.
    iIntros (v2' ? Heq). subst. inversion Heq; subst.
    rewrite to_of_val. naive_solver.
  Unshelve. eauto.
Qed.
