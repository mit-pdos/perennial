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
    (|={⊤,∅}=> |={∅}▷=>^(steps_sum (perennial_num_laters_per_step) ncurrent n) |={∅, ⊤}=>
     |={⊤, ⊤}_2=> ∀ Hc', NC 1 ={⊤}=∗ (∃ t' : pbundleG T Σ, step_fupdN_fresh (S (n + ncurrent)) ns Hc' t' P))%I
  end.

Lemma step_fupdN_fresh_pattern_fupd {H: invG Σ} n (Q Q': iProp Σ):
  (|={⊤,⊤}_n=> |={⊤,⊤}_2=> Q) -∗ (Q ={⊤}=∗ Q') -∗
  (|={⊤,⊤}_n=> |={⊤,⊤}_2=> Q').
Proof.
  iIntros "H Hwand". simpl.
  iApply (step_fupdN_wand with "H").
  iIntros "H".
  iMod "H". iModIntro.
  iMod "H". iModIntro.
  iApply (step_fupd_wand with "H").
  iIntros "H".
  iApply (step_fupd_wand with "H").
  iMod 1 as "H". by iMod ("Hwand" with "[$]").
Qed.

Lemma step_fupdN_fresh_pattern_bupd {H: invG Σ} n (Q Q': iProp Σ):
  (|={⊤,⊤}_n=> |={⊤,⊤}_2=> Q) -∗ (Q ==∗ Q') -∗
  (|={⊤,⊤}_n=> |={⊤,⊤}_2=> Q').
Proof.
  iIntros "H Hwand". iApply (step_fupdN_fresh_pattern_fupd with "H").
  iIntros. by iMod ("Hwand" with "[$]").
Qed.

Lemma step_fupdN_fresh_pattern_wand {H: invG Σ} n (Q Q': iProp Σ):
  (|={⊤,⊤}_n=> |={⊤,⊤}_2=> Q) -∗ (Q -∗ Q') -∗
  (|={⊤,⊤}_n=> |={⊤,⊤}_2=> Q').
Proof.
  iIntros "H Hwand". iApply (step_fupdN_fresh_pattern_bupd with "H").
  iIntros. by iApply "Hwand".
Qed.

Lemma step_fupdN_fresh_pattern_plain {H: invG Σ} n (Q: iProp Σ) `{!Plain Q}:
  (|={⊤}[∅]▷=>^n |={⊤, ∅}=> ▷ Q) -∗
  (|={⊤}=> ▷^(S n) Q).
Proof.
  iIntros "H".
  iDestruct (step_fupdN_wand with "H []") as "H".
  { iApply fupd_plain_mask_empty. }
  destruct n.
  { iMod "H". eauto. }
  rewrite -step_fupdN_S_fupd.
  iDestruct (step_fupdN_plain with "H") as "H".
  iMod "H". iModIntro. iNext. rewrite -later_laterN laterN_later. iNext. by iMod "H".
Qed.

Lemma step_fupdN_fresh_pattern_plain' {H: invG Σ} n (Q: iProp Σ) `{!Plain Q}:
  (|={⊤}[∅]▷=>^(S n) |={⊤, ∅}_2=> Q) -∗
  (|={⊤}=> ▷^(S (S (S (S n)))) Q).
Proof.
  iIntros "H".
  iDestruct (step_fupdN_wand with "H []") as "H".
  { iApply step_fupdN_inner_plain. }
  rewrite -step_fupdN_S_fupd.
  iMod (step_fupdN_plain with "H") as "H".
  iModIntro. iNext. rewrite -?later_laterN ?laterN_later. iNext.
  iMod "H". eauto.
Qed.

Lemma step_fupdN_fresh_pattern_plain'' {H: invG Σ} n (Q: iProp Σ) `{!Plain Q}:
  (|={⊤}[∅]▷=>^(S n) |={⊤, ⊤}_2=> Q) -∗
  (|={⊤}=> ▷^(S (S (S (S n)))) Q).
Proof.
  iIntros "H".
  iDestruct (step_fupdN_wand with "H []") as "H".
  { iApply step_fupdN_inner_plain'. }
  rewrite -step_fupdN_S_fupd.
  iMod (step_fupdN_plain with "H") as "H".
  iModIntro. iNext. rewrite -?later_laterN ?laterN_later. iNext.
  iMod "H". eauto.
Qed.

Lemma step_fupdN_fresh_wand ncurr (ns: list nat) Hc0 t0 Q Q':
  step_fupdN_fresh ncurr (ns) Hc0 t0 Q -∗ (∀ Hc t, Q Hc t -∗ Q' Hc t)
  -∗ step_fupdN_fresh ncurr ns Hc0 t0 Q'.
Proof.
  revert Hc0 t0 ncurr.
  induction ns => ???.
  - iIntros "H Hwand". iApply "Hwand". eauto.
  - iIntros "H Hwand". rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    iApply (step_fupdN_fresh_pattern_wand with "H [Hwand]").
    iIntros "H". (* iMod "H". iModIntro. *)
    iIntros (Hc') "HNC". iSpecialize ("H" $! Hc' with "[$]"). iMod "H" as (?) "H".
    iExists _. iModIntro. iApply (IHns with "H"). eauto.
Qed.

Fixpoint fresh_later_count f ncurr (ns: list nat) :=
  match ns with
  | [] => 0
  | n :: ns' => S (S (S (steps_sum f ncurr n)))
                 + fresh_later_count f (S (n + ncurr)) ns'
  end.

Lemma wptp_recv_strong_normal_adequacy Φ Φinv Φr κs' s k Hc t n ns ncurr r1 e1 t1 κs t2 σ1 g1 σ2 g2 :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) Normal →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ncurr (κs ++ κs') -∗
  wpr s k Hc t ⊤ e1 r1 Φ Φinv Φr -∗
  wptp s k t1 -∗ NC 1-∗ step_fupdN_fresh ncurr ns Hc t (λ Hc' t',
    ⌜ Hc' = Hc ∧ t' = t ⌝ ∗
    (|={⊤,⊤}_(steps_sum num_laters_per_step ncurr n)=> ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ▷^(S (S (num_laters_per_step (n + ncurr)))) (⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 g2 ⌝) ∗
    state_interp σ2 (length t2') ∗
    global_state_interp g2 (n + ncurr) κs' ∗
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
  iApply (step_fupdN_wand with "H"); auto.
Qed.

Fixpoint sum_crash_steps ns :=
  match ns with
  | [] => 0
  | n :: ns => (S n) + (sum_crash_steps ns)
  end.

Lemma wptp_recv_strong_crash_adequacy Φ Φinv Φinv' Φr κs' s k Hc t ncurr ns n r1 e1 t1 κs t2 σ1 g1 σ2 g2 :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) Crashed →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ncurr (κs ++ κs') -∗
  wpr s k Hc t ⊤ e1 r1 Φ Φinv Φr -∗
  □ (∀ Hc' t', Φinv Hc' t' -∗ □ Φinv' Hc' t') -∗
  wptp s k t1 -∗ NC 1-∗ step_fupdN_fresh ncurr ns Hc t (λ Hc' t',
    let ntot := (steps_sum perennial_num_laters_per_step (ncurr + sum_crash_steps ns)
                           n)  in
    (|={⊤,∅}=> |={∅}▷=>^ ntot |={∅, ⊤}=> (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ▷^(S (S (num_laters_per_step $ n + sum_crash_steps ns + ncurr)))
        (⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 g2⌝) ∗
    state_interp σ2 (length t2') ∗
    global_state_interp g2 (n + sum_crash_steps ns + ncurr) κs' ∗
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
  iMod "H". iModIntro.
  iApply (step_fupdN_wand _ _ (steps_sum perennial_num_laters_per_step ncurr n') with "H").
  iIntros "H".
  iMod "H".
  iModIntro. iMod (fupd_mask_subseteq ∅) as "Hclo"; first set_solver.
  iModIntro. iModIntro. iNext.
  iMod ("Hclo") as "_".
  iMod (fupd_mask_subseteq ∅) as "Hclo"; first set_solver.
  iMod ("Hclo") as "_".
  iDestruct "H" as (e2 t2' ?) "(H&Hσ&Hg&HC)".
  iMod ("H" with "[//] Hσ Hg") as "H".
  iMod (fupd_mask_subseteq ∅) as "Hclo"; first set_solver. do 2 iModIntro. iNext.
  iModIntro.
  iMod ("Hclo") as "_".
  iModIntro.
  destruct s0.
  - iIntros (Hc') "HNC". iSpecialize ("H" $! Hc' with "[$]").
    iMod "H" as (t' Heq' Heqpf') "(Hσ&Hg&Hr&HNC)".
    iDestruct "Hr" as "(_&Hr)".
    simpl in *.
    iPoseProof (IH with "[Hσ] [Hg] Hr [] [] HNC") as "H"; eauto.
    iExists _. iModIntro. simpl. eauto.
    assert (n + sum_crash_steps ns' + S (n' + ncurr) =
            (n + S (n' + sum_crash_steps ns') + ncurr)) as -> by lia.
    iApply (step_fupdN_fresh_wand with "H").
    iIntros (??) "H".
    iMod "H". iModIntro.
    assert ((S (n' + ncurr + sum_crash_steps ns')) =
        (ncurr + S (n' + sum_crash_steps ns'))) as -> by lia. auto.
  - iIntros (Hc') "HNC".
    iMod ("H" $! Hc' with "[$]") as (t' Heq' Heqpf') "(Hσ&Hg&Hr&HNC)".
    iExists t'.
    iAssert (□Φinv' Hc' t')%I as "#Hinv'".
    { iDestruct "Hr" as "(Hr&_)".
      iApply "Hinv". eauto.
    }
    iDestruct "Hr" as "(_&Hr)".
    iDestruct (wptp_recv_strong_normal_adequacy with "[Hσ] [Hg] [Hr] [] HNC") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H").
    iModIntro.
    iIntros (??) "H".
    iDestruct "H" as ((?&?)) "H". subst.
    iClear "HC". simpl.
    assert (ns' = []) as ->; first by (eapply nrsteps_normal_empty_prefix; eauto).
    simpl.
    assert (S (n' + ncurr) = (ncurr + S (n' + 0))) as -> by lia.
    rewrite perennial_num_laters_per_step_spec.
    iApply (step_fupdN_wand with "H").
    iMod 1 as "H".
    iFrame "Hinv'". iModIntro. rewrite Nat.add_0_r.
    assert (n + (ncurr + S n') =  (n + S n' + ncurr)) as -> by lia. auto.
Qed.

Lemma wptp_recv_strong_adequacy Φ Φinv Φinv' Φr κs' s k Hc t ns n r1 e1 t1 κs t2 σ1 g1 ncurr σ2 g2 stat :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) stat →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 ncurr (κs ++ κs') -∗
  wpr s k Hc t ⊤ e1 r1 Φ Φinv Φr -∗
  □ (∀ Hc' t', Φinv Hc' t' -∗ □ Φinv' Hc' t') -∗
  wptp s k t1 -∗ NC 1-∗ step_fupdN_fresh ncurr ns Hc t (λ Hc' t',
    let ntot := (steps_sum perennial_num_laters_per_step (ncurr + sum_crash_steps ns)
                           n)  in
    (|={⊤,∅}=> |={∅}▷=>^ ntot |={∅, ⊤}=> (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ▷^(S (S (num_laters_per_step $ n + sum_crash_steps ns + ncurr)))
        (⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 g2 ⌝) ∗
    state_interp σ2 (length t2') ∗
    global_state_interp g2 (n + sum_crash_steps ns + ncurr) κs' ∗
    (match stat with
     | Normal => ⌜ Hc' = Hc ∧ t' = t ⌝ ∗ from_option Φ True (to_val e2)
     | Crashed => from_option (Φr Hc' t') True (to_val e2) ∗ □ Φinv' Hc' t'
     end)  ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1))).
Proof.
  intros. destruct stat.
  - iIntros. iDestruct (wptp_recv_strong_crash_adequacy with "[$] [$] [$] [$] [$] [$]") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H").
    iIntros (??) "H".
    iApply (step_fupdN_wand with "H"); auto.
    iIntros "H".
    iMod "H" as (???) "(?&H&?&?&?)". iExists _, _.
    repeat (iSplitL ""; try iFrame; eauto).
  - iIntros. iDestruct (wptp_recv_strong_normal_adequacy with "[$] [$] [$] [$] [$]") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H").
    iIntros (??) "H".
    iDestruct "H" as ((?&?)) "H". subst.
    assert (ns = []) as ->; first by (eapply nrsteps_normal_empty_prefix; eauto).
    simpl. rewrite Nat.add_0_r.
    iMod "H". iModIntro.
    rewrite perennial_num_laters_per_step_spec.
    iApply (step_fupdN_wand with "H"); auto.
    iIntros "H".
    iMod "H" as (???) "(?&H&?&?&?)". iExists _, _.
    iSplitL ""; first eauto. iFrame.  rewrite Nat.add_0_r.
    iFrame.
    repeat (iSplitL ""; try iFrame; eauto).
Qed.

End recovery_adequacy.

Lemma step_fupdN_fresh_plain {Λ CS T Σ} `{!invPreG Σ} `{!crashPreG Σ} P `{!Plain P} ns ncurr f k:
  (∀ (Hi': invG Σ) Hc', NC 1-∗ |={⊤}=>
   ∃ (pG: perennialG Λ CS T Σ)
     (Hpf1: ∀ Hc t, @iris_invG _ _ (perennial_irisG Hc t) = Hi')
     (Hpf2: perennial_num_laters_per_step = f) t,
     |={⊤}=> step_fupdN_fresh ncurr ns Hc' t
                  (λ _ _, |={⊤,⊤}_k=> P)) -∗
  ▷^(fresh_later_count f ncurr ns + S k) P.
Proof.
  iIntros "H".
  iMod wsat_alloc' as (Hinv) "(Hw&HE)".
  iSpecialize ("H" $! Hinv).
  rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
  iApply (bupd_plain (▷^(_) P)%I); try (iPureIntro; apply _).
  iMod NC_alloc as (Hc) "HNC".
  rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
  iDestruct (ownE_weaken _ (AlwaysEn ∪ MaybeEn ⊤) with "HE") as "HE"; first by set_solver.
  rewrite plus_comm. iEval (simpl).
  iMod ("H" with "[$] [$]") as "[>Hw [>HE >H]]"; eauto.
  iDestruct "H" as (pG Hpf1 Hpf2 t) "H".
  iMod ("H" with "[$]") as "[>Hw [>HE >H]]"; eauto.

  (* Have to strengthen the induction hypothesis to not lose wsat and ownE *)
  iAssert (|={⊤}=> ▷ ▷^(k + fresh_later_count f ncurr ns) P)%I with "[H]" as "Hgoal"; last first.
  {
    rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
    iMod ("Hgoal" with "[$]") as "[Hw [HE >H]]"; eauto.
  }

  iInduction ns as [| n' ns] "IH" forall (t Hc ncurr).
  - rewrite /step_fupdN_fresh.
    simpl. iApply step_fupdN_inner_plain'.
    iMod "H". iModIntro. rewrite Nat_iter_add. iApply (step_fupdN_wand with "H").
    iIntros "H".
    iApply step_fupdN_later; auto.
  - iMod NC_alloc as (Hc') "HNC".
    rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    iDestruct (step_fupdN_fresh_pattern_fupd _ _
                  (▷^(S k + fresh_later_count f (S (n' + ncurr)) ns) P)%I
                 with "H [IH HNC]") as "H".
    { iIntros "H".
      iSpecialize ("H" with "[$]").
      rewrite ?Hpf1.
      rewrite ?Hpf2.
      iMod "H". iDestruct "H" as (t') "H".
      iMod ("IH" with "H") as "H". iModIntro; eauto.
    }
    rewrite step_fupdN_inner_plus.
    iPoseProof (step_fupdN_inner_plain' with "H") as "H".
    simpl.
    rewrite ?Hpf1.
    rewrite ?Hpf2.
    iMod "H". iModIntro.
    rewrite -?laterN_later.
    rewrite -?laterN_plus.
    iNext.
    assert ((S (crash_adequacy.steps_sum f ncurr n' + 2) + (k + fresh_later_count f (S (n' + ncurr)) ns))
             =(k + S (S (S (crash_adequacy.steps_sum f ncurr n' + fresh_later_count f (S (n' + ncurr)) ns)))))
           as Heq.
    { lia. }
    rewrite Heq.
    iNext. auto.
Qed.

Lemma step_fupdN_fresh_soundness {Λ CS T Σ} `{!invPreG Σ} `{!crashPreG Σ} (φ : Prop) ns ncurr k k2 f:
  (∀ (Hi: invG Σ) (Hc: crashG Σ), NC 1 ={⊤}=∗
    ∃ (pG: perennialG Λ CS T Σ) (Hpf1: ∀ Hc t, @iris_invG _ _ (perennial_irisG Hc t) = Hi)
     (Hpf2: perennial_num_laters_per_step = f) t0,
      (|={⊤}=> step_fupdN_fresh ncurr ns Hc t0 (λ _ _,
       |={⊤,⊤}_k=> ▷^k2 ⌜φ⌝))%I) →
  φ.
Proof.
  intros Hiter.
  eapply (soundness (M:=iResUR Σ) _  (_ + k2)); simpl.
  rewrite laterN_plus.
  iApply step_fupdN_fresh_plain. iIntros (Hinv Hc). iApply Hiter.
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

Corollary wp_recv_adequacy_inv Σ Λ CS (T: ofe) `{!invPreG Σ} `{!crashPreG Σ} s k e r σ g φ φr φinv Φinv f:
  (∀ `{Hinv : !invG Σ} `{Hc: !crashG Σ} κs,
     ⊢ |={⊤}=> ∃ (t: pbundleG T Σ)
         (stateI : pbundleG T Σ → state Λ → nat → iProp Σ)
         (global_stateI : pbundleG T Σ → global_state Λ → nat → list (observation Λ) → iProp Σ)
         (fork_post : pbundleG T Σ → val Λ → iProp Σ) Hpf1 Hpf2 Hpf3,
        let _ : perennialG Λ CS _ Σ :=
            PerennialG _ _ T Σ
              (λ Hc t,
               IrisG Λ Σ Hinv Hc (stateI t) (global_stateI t) (fork_post t) f (Hpf1 Hc t)) Hpf2 f Hpf3
               in
       □ (∀ σ nt, stateI t σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
       □ (∀ Hc t', Φinv t Hinv Hc t' -∗ □ ∀ σ nt, stateI t' σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
       stateI t σ 0 ∗ global_stateI t g 0 κs ∗
       wpr s k Hc t ⊤ e r (λ v, ⌜φ v⌝) (Φinv t Hinv) (λ _ _ v, ⌜φr v⌝)) →
  recv_adequate (CS := CS) s e r σ g (λ v _ _, φ v) (λ v _ _, φr v) (λ σ _, φinv σ).
Proof.
  intros Hwp.
  apply recv_adequate_alt.
  intros t2 σ2 g2 stat [n [κs H]]%erased_rsteps_nrsteps.
  destruct (nrsteps_snoc _ _ _ _ _ _ H) as (ns'&n'&->).
  eapply (step_fupdN_fresh_soundness _ ns' 0
              (crash_adequacy.steps_sum f (sum_crash_steps ns') n')
              (S $ S $ (f (n' + sum_crash_steps ns' + 0))))=> Hinv Hc.
  iIntros "HNC".
  iMod (Hwp Hinv Hc κs) as (t stateI global_stateI Hfork_post Hpf1 Hpf2 Hpf3) "(#Hinv1&#Hinv2&Hσ&Hg&H)".
  iModIntro.
  set (pG :=
          PerennialG _ _ T Σ
            (λ Hc t, IrisG Λ Σ Hinv Hc (stateI t) (global_stateI t) (Hfork_post t) f (Hpf1 Hc t))
            Hpf2 f Hpf3).
  iExists pG.
  iDestruct (wptp_recv_strong_adequacy
                _ _ (λ Hc t, (∀ σ nt, stateI t σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝))%I
               _ [] with "[Hσ] [Hg] [H] [] [] HNC") as "H"; eauto.
  { rewrite app_nil_r. eauto. }
  iExists _.
  unshelve (iExists _); first by (rewrite //=).
  iExists t.
  iModIntro.
  iApply (step_fupdN_fresh_wand with "H").
  iIntros (??) "H".
  rewrite /perennial_num_laters_per_step.
  iApply (step_fupdN_wand with "H"); auto.
  iIntros "H".
  iMod "H" as (v2 ??) "(Hnstuck&Hσ&Hg&Hv&Hfpost&HNC)".
  destruct stat.
  - iDestruct "Hv" as "(Hv&#Hinv)".
    rewrite ?ncfupd_eq /ncfupd_def.
    iApply fupd_plain_mask.
    iMod ("Hinv" with "[$] [$]") as "(Hp&HNC)".
    iDestruct "Hp" as %?. iModIntro.
    iModIntro.
    rewrite Hpf3. iNext. iNext.
    iSplit; [| iSplit]; eauto.
    iIntros (v2' ? Heq). subst. inversion Heq; subst.
    rewrite to_of_val. naive_solver.
  - iDestruct "Hv" as "(Heq1&Hv)".
    iDestruct "Heq1" as %(?&?); subst.
    iApply fupd_plain_mask.
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
