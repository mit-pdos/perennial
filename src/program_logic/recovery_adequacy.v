From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.program_logic Require Export weakestpre.
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
Implicit Types Φinv : invG Σ → crashG Σ → pbundleG T Σ → iProp Σ.
Implicit Types Φc : invG Σ → crashG Σ → pbundleG T Σ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Notation wptp s k t := ([∗ list] ef ∈ t, WPC ef @ s; k; ⊤ {{ fork_post }} {{ True }})%I.

Fixpoint step_fupdN_fresh (ns: list nat) Hi0 (Hc0: crashG Σ) t0
         (P: invG Σ → crashG Σ → pbundleG T Σ → iProp Σ) {struct ns} :=
  match ns with
  | [] => P Hi0 Hc0 t0
  | (n :: ns) =>
    (|={⊤}[∅]▷=>^(S (S n)) |={⊤, ∅}_2=>
     ∀ Hi' Hc', NC 1 ={⊤}=∗ (∃ t' : pbundleG T Σ, step_fupdN_fresh ns Hi' Hc' t' P))%I
  end.

Lemma step_fupdN_fresh_snoc (ns: list nat) n Hi0 Hc0 t0 Q:
  step_fupdN_fresh (ns ++ [n]) Hi0 Hc0 t0 Q ≡
  step_fupdN_fresh (ns) Hi0 Hc0 t0
    (λ Hi Hc' _, |={⊤}[∅]▷=>^(S (S n)) |={⊤, ∅}_2=> ∀ Hi' Hc', NC 1={⊤}=∗ ∃ t', Q Hi' Hc' t')%I.
Proof.
  apply (anti_symm (⊢)%I).
  - revert Hi0 Hc0 t0 Q.
    induction ns => ????; first by auto.
    iIntros "H".
    iApply (step_fupdN_wand ⊤ ∅ with "[H] []"); auto.
    iIntros "H".
    iMod "H". iModIntro. iMod "H". iModIntro. iNext.
    iMod "H". iModIntro. iMod "H". iModIntro. iNext.
    iMod "H". iModIntro. iMod "H". iModIntro.
    iIntros (??) "HNC".
    iMod ("H" $! _ _ with "[$]") as (?) "H".
    iExists _. by iApply IHns.
  - revert Hi0 Hc0 t0 Q.
    induction ns => ???? //=.
    do 3 f_equiv.
    iIntros "H".
    iApply (step_fupdN_wand with "H"); auto.
    iNext. iIntros "H".
    iMod "H". iModIntro.
    iMod "H". do 2 iModIntro.
    iMod "H". iModIntro.
    iMod "H". do 2 iModIntro.
    iMod "H". iModIntro.
    iMod "H". iModIntro.
    iIntros (??) "HNC".
    iMod ("H" $! _ _ with "[$]") as (?) "H".
    iExists _. by iApply IHns.
Qed.

Lemma step_fupdN_fresh_pattern_wand {H: invG Σ} n (Q Q': iProp Σ):
  (|={⊤}[∅]▷=>^n |={⊤, ∅}_2=> Q) -∗ (Q -∗ Q') -∗
  (|={⊤}[∅]▷=>^n |={⊤, ∅}_2=> Q').
Proof.
  iIntros "H Hwand". simpl.
  iApply (step_fupdN_wand with "H").
  iIntros "H". iMod "H". iModIntro.
  iMod "H". do 2 iModIntro.
  iMod "H". iModIntro.
  iMod "H". do 2 iModIntro.
  iMod "H". iModIntro.
  iMod "H". iModIntro.
  by iApply "Hwand".
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

Lemma step_fupdN_fresh_wand (ns: list nat) Hi0 Hc0 t0 Q Q':
  step_fupdN_fresh (ns) Hi0 Hc0 t0 Q -∗ (∀ Hinv Hc t, Q Hinv Hc t -∗ Q' Hinv Hc t)
  -∗ step_fupdN_fresh ns Hi0 Hc0 t0 Q'.
Proof.
  revert Hi0 Hc0 t0.
  induction ns => ???.
  - iIntros "H Hwand". iApply "Hwand". eauto.
  - iIntros "H Hwand". rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    iApply (step_fupdN_fresh_pattern_wand with "H [Hwand]").
    iIntros "H". (* iMod "H". iModIntro. *)
    iIntros (Hi' Hc') "HNC". iSpecialize ("H" $! Hi' Hc' with "[$]"). iMod "H" as (?) "H".
    iExists _. iApply (IHns with "H"). eauto.
Qed.

Fixpoint fresh_later_count (ns: list nat) :=
  match ns with
  | [] => (S (S (S O)))
  | n :: ns' => (S (S (S (S (S n))))) + fresh_later_count ns'
  end.

Lemma step_fupdN_fresh_plain `{!invPreG Σ} `{!crashPreG Σ} P `{!Plain P} ns n:
  (∀ Hinv' Hc', NC 1-∗ |={⊤}=> ∃ t, step_fupdN_fresh ns Hinv' Hc' t
                  (λ _ _ _, |={⊤}[∅]▷=>^(S n) |={⊤, ∅}_2=> P)) -∗
  ▷^(fresh_later_count ns + S n) P.
Proof.
  iIntros "H".
  iInduction ns as [| n' ns] "IH".
  - rewrite /step_fupdN_fresh.
    iApply (bupd_plain (▷^(_) P)%I); try (iPureIntro; apply _).
    iMod wsat_alloc' as (Hinv) "(Hw&HE)".
    iMod NC_alloc as (Hc) "HNC".
    iSpecialize ("H" $! Hinv Hc with "HNC").
    rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
    iDestruct (ownE_weaken _ (AlwaysEn ∪ MaybeEn ⊤) with "HE") as "HE"; first by set_solver.
    iMod ("H" with "[$]") as "[>Hw [>HE >H]]".
    iDestruct ("H") as (_) "H".
    iDestruct (step_fupdN_fresh_pattern_plain' _ (P)%I with "H") as "H".
    rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
    iMod ("H" with "[$]") as "[Hw [HE >?]]"; eauto.
  - iMod wsat_alloc' as (Hinv) "(Hw&HE)".
    iMod NC_alloc as (Hc) "HNC".
    iSpecialize ("H" $! Hinv).
    rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
    iDestruct (ownE_weaken _ (AlwaysEn ∪ MaybeEn ⊤) with "HE") as "HE"; first by set_solver.
    iMod ("H" with "HNC [$]") as "[>Hw [>HE >H]]".
    iDestruct "H" as (t) "H".
    rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    iDestruct (step_fupdN_fresh_pattern_wand _ _
                  (▷^(fresh_later_count ns + _) P)%I
                 with "H [IH]") as "H".
    { iIntros "H". iApply "IH". iIntros. iMod ("H" with "[$]"). iModIntro. eauto. }
    iDestruct (step_fupdN_fresh_pattern_plain' with "H") as "H".
    rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
    iMod ("H" with "[$]") as "[Hw [HE >H]]".
    simpl. rewrite ?laterN_plus. iApply "H".
Qed.

(* XXX this probably needs to be tweaked. *)
Lemma step_fupdN_fresh_soundness `{!invPreG Σ} `{!crashPreG Σ} (φ : Prop) ns n:
  (∀ (Hinv : invG Σ) (Hc: crashG Σ), NC 1-∗ (|={⊤}=> (∃ t0, step_fupdN_fresh ns Hinv Hc t0
                             (λ _ _ _, |={⊤}[∅]▷=>^((S (S n))) |={⊤, ∅}_2=> ⌜φ⌝)))%I) →
  φ.
Proof.
  intros Hiter.
  eapply (soundness (M:=iResUR Σ) _  (fresh_later_count ns + _)); simpl.
  rewrite laterN_plus.
  iApply step_fupdN_fresh_plain. iIntros (Hinv Hc). iApply Hiter.
Qed.

(*
Notation "|={ E }=>_( t ) Q" := (fupd (FUpd := t) E E Q)
 (at level 99) : bi_scope.
Notation "P ={ E }=∗_ t Q" := (P -∗ |={E}=>_(t) Q)%I
 (at level 99) : bi_scope.
*)

Lemma wptp_recv_strong_normal_adequacy Φ Φinv Φr κs' s k Hi Hc t n ns r1 e1 t1 κs t2 σ1 σ2 :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, σ1) κs (t2, σ2) Normal →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  wpr s k Hi Hc t ⊤ e1 r1 Φ Φinv Φr -∗
  wptp s k t1 -∗ NC 1-∗ step_fupdN_fresh ns Hi Hc t (λ Hi' Hc' t',
    ⌜ Hi' = Hi ∧ Hc' = Hc ∧ t' = t ⌝ ∗
    (|={⊤}[∅]▷=>^(S n) ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1)).
Proof.
  iIntros (Hstep) "Hσ He Ht HNC".
  inversion Hstep. subst.
  iPoseProof (wptp_strong_adequacy with "Hσ [He] Ht") as "H".
  { eauto. }
  {rewrite wpr_unfold /wpr_pre. iApply "He". }
  rewrite perennial_crashG.
  iSpecialize ("H" with "[$]").
  assert (ns = []) as ->;
    first by (eapply nrsteps_normal_empty_prefix; eauto).
  inversion H. subst.
  rewrite /step_fupdN_fresh.
  rewrite perennial_invG.
  iSplitL ""; first by eauto.
  iApply (step_fupdN_wand with "H"); auto.
Qed.

Lemma wptp_recv_strong_crash_adequacy Φ Φinv Φinv' Φr κs' s k Hi Hc t ns n r1 e1 t1 κs t2 σ1 σ2 :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, σ1) κs (t2, σ2) Crashed →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  wpr s k Hi Hc t ⊤ e1 r1 Φ Φinv Φr -∗
  □ (∀ Hi' Hc' t', Φinv Hi' Hc' t' -∗ □ Φinv' Hi' Hc' t') -∗
  wptp s k t1 -∗ NC 1-∗ step_fupdN_fresh ns Hi Hc t (λ Hi' Hc' t',
    (|={⊤}[∅]▷=>^(S (S n)) ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    from_option (Φr Hi' Hc' t') True (to_val e2) ∗
    □ Φinv' Hi' Hc' t' ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1)).
Proof.
  revert Hi Hc t e1 t1 κs κs' t2 σ1 σ2 Φ.
  induction ns as [|n' ns' IH] => Hi Hc t e1 t1 κs κs' t2 σ1 σ2 Φ.
  { rewrite app_nil_l.
    inversion 1.
    match goal with
    | [ H : nrsteps _ _ _ _ _ _ |- _ ] => inversion H
    end.
  }
  iIntros (Hsteps) "Hσ He #Hinv Ht HNC".
  inversion_clear Hsteps as [|?? [t1' σ1'] ????? s0].
  rewrite {1}/step_fupdN_fresh -/step_fupdN_fresh.
  destruct ρ2 as (?&σ2_pre_crash).
  rewrite -assoc wpr_unfold /wpr_pre.
  rewrite Nat_iter_S.
  iApply (step_fupdN_later _ _ 1); first by set_solver+. iNext.
  iPoseProof (@wptp_strong_crash_adequacy with "[$] [$] [$]") as "H"; eauto.
  rewrite perennial_crashG perennial_invG.
  iSpecialize ("H" with "[$]").
  iApply (step_fupdN_wand _ _ (S n') with "H").
  iIntros "H".
  iMod "H". iModIntro. iModIntro. iNext.
  iDestruct "H" as (e2 t2' ?) "(H&Hσ&HC)".
  iMod ("H" with "[//] Hσ") as "H". iModIntro.
  iModIntro. iNext. do 2 iModIntro.
  destruct s0.
  - iIntros (Hi' Hc') "HNC". iSpecialize ("H" $! Hi' Hc' with "[$]").
    iMod "H" as (t') "(Hσ&Hr&HNC)".
    iDestruct "Hr" as "(_&Hr)".
    iPoseProof (IH with "[Hσ] Hr [] [] HNC") as "H"; eauto.
  - iIntros (Hi' Hc') "HNC".
    iMod ("H" $! Hi' Hc' with "[$]") as (t') "(Hσ&Hr&HNC)".
    iExists t'.
    iAssert (□Φinv' Hi' Hc' t')%I as "#Hinv'".
    { iDestruct "Hr" as "(Hr&_)".
      iApply "Hinv". eauto.
    }
    iDestruct "Hr" as "(_&Hr)".
    iDestruct (wptp_recv_strong_normal_adequacy with "[Hσ] [Hr] [] HNC") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H").
    iModIntro.
    iIntros (???) "H".
    iDestruct "H" as ((?&?&?)) "H". subst.
    iClear "HC".
    iApply (step_fupdN_wand with "H"); auto.
    iFrame "Hinv'". iApply step_fupd_intro; first by set_solver. iNext. eauto.
Qed.

Lemma wptp_recv_strong_adequacy Φ Φinv Φinv' Φr κs' s k Hi Hc t ns n r1 e1 t1 κs t2 σ1 σ2 stat :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, σ1) κs (t2, σ2) stat →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  wpr s k Hi Hc t ⊤ e1 r1 Φ Φinv Φr -∗
  □ (∀ Hi' Hc' t', Φinv Hi' Hc' t' -∗ □ Φinv' Hi' Hc' t') -∗
  wptp s k t1 -∗ NC 1-∗ step_fupdN_fresh ns Hi Hc t (λ Hi' Hc' t',
    (|={⊤}[∅]▷=>^(S (S n)) ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    (match stat with
     | Normal => ⌜ Hi' = Hi ∧ Hc' = Hc ∧ t' = t ⌝ ∗ from_option Φ True (to_val e2)
     | Crashed => from_option (Φr Hi' Hc' t') True (to_val e2) ∗ □ Φinv' Hi' Hc' t'
     end)  ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1)).
Proof.
  intros. destruct stat.
  - iIntros. iDestruct (wptp_recv_strong_crash_adequacy with "[$] [$] [$] [$] [$]") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H").
    iIntros (???) "H".
    iApply (step_fupdN_wand with "H"); auto.
    iIntros "H".
    iDestruct "H" as (????) "(H&?&?&?)". iExists _, _.
    repeat (iSplitL ""; try iFrame; eauto).
  - iIntros. iDestruct (wptp_recv_strong_normal_adequacy with "[$] [$] [$] [$]") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H").
    iIntros (???) "H".
    iDestruct "H" as ((?&?&?)) "H". subst.
    iApply (step_fupdN_wand with "H"); auto.
    iApply step_fupd_intro; first by set_solver. iNext.
    iIntros "H".
    iDestruct "H" as (????) "(H&?&?)". iExists _, _.
    repeat (iSplitL ""; try iFrame; eauto).
Qed.

End recovery_adequacy.

Record recv_adequate {Λ CS} (s : stuckness) (e1 r1: expr Λ) (σ1 : state Λ)
    (φ φr: val Λ → state Λ → Prop) (φinv: state Λ → Prop)  := {
  recv_adequate_result_normal t2 σ2 v2 :
   erased_rsteps (CS := CS) r1 ([e1], σ1) (of_val v2 :: t2, σ2) Normal →
   φ v2 σ2;
  recv_adequate_result_crashed t2 σ2 v2 :
   erased_rsteps (CS := CS) r1 ([e1], σ1) (of_val v2 :: t2, σ2) Crashed →
   φr v2 σ2;
  recv_adequate_not_stuck t2 σ2 e2 stat :
   s = NotStuck →
   erased_rsteps (CS := CS) r1 ([e1], σ1) (t2, σ2) stat →
   e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2);
  recv_adequate_inv t2 σ2 stat :
   erased_rsteps (CS := CS) r1 ([e1], σ1) (t2, σ2) stat →
   φinv σ2
}.

Lemma recv_adequate_alt {Λ CS} s e1 r1 σ1 (φ φr : val Λ → state Λ → Prop) φinv :
  recv_adequate (CS := CS) s e1 r1 σ1 φ φr φinv ↔ ∀ t2 σ2 stat,
    erased_rsteps (CS := CS) r1 ([e1], σ1) (t2, σ2) stat →
      (∀ v2 t2', t2 = of_val v2 :: t2' →
                 match stat with
                   | Normal => φ v2 σ2
                   | Crashed => φr v2 σ2
                 end) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2)) ∧
      (φinv σ2).
Proof.
  split.
  - intros [] ?? []; naive_solver.
  - constructor; naive_solver.
Qed.

Corollary wp_recv_adequacy_inv Σ Λ CS (T: ofeT) `{!invPreG Σ} `{!crashPreG Σ} s k e r σ φ φr φinv Φinv :
  (∀ `{Hinv : !invG Σ} `{Hc: !crashG Σ} κs,
     ⊢ |={⊤}=> ∃ (t: pbundleG T Σ)
         (stateI : invG Σ → pbundleG T Σ→ state Λ → list (observation Λ) → iProp Σ)
         (fork_post : pbundleG T Σ → val Λ → iProp Σ) Hpf1 Hpf2,
        let _ : perennialG Λ CS _ Σ :=
            PerennialG _ _ T Σ
              (λ Hi Hc t,
               IrisG Λ Σ Hi Hc (λ σ κs _, stateI Hi t σ κs)
                    (fork_post t)) Hpf1 Hpf2
               in
       □ (∀ σ κ, stateI Hinv t σ κ -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
       □ (∀ Hi Hc t, Φinv Hi Hc t -∗ □ ∀ σ κ, stateI Hi t σ κ -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
       stateI Hinv t σ κs ∗ wpr s k Hinv Hc t ⊤ e r (λ v, ⌜φ v⌝) Φinv (λ _ _ _ v, ⌜φr v⌝)) →
  recv_adequate (CS := CS) s e r σ (λ v _, φ v) (λ v _, φr v) φinv.
Proof.
  intros Hwp.
  apply recv_adequate_alt.
  intros t2 σ2 stat [n [κs H]]%erased_rsteps_nrsteps.
  destruct (nrsteps_snoc _ _ _ _ _ _ H) as (ns'&n'&->).
  eapply (step_fupdN_fresh_soundness _ ns' n')=> Hinv Hc.
  iIntros "HNC".
  iMod (Hwp Hinv Hc κs) as (t stateI Hfork_post Hpf1 Hpf2) "(#Hinv1&#Hinv2&Hw&H)".
  iModIntro. iExists _.
  iDestruct (wptp_recv_strong_adequacy
               (perennialG0 :=
          PerennialG _ _ T Σ
            (λ Hi Hc t,
             IrisG Λ Σ Hi Hc (λ σ κs _, stateI Hi t σ κs)
                  (Hfork_post t)) Hpf1 Hpf2) _ _ (λ Hi Hc t, (∀ σ κ, stateI Hi t σ κ -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝))%I
               _ [] with "[Hw] [H] [] [] HNC") as "H"; eauto.
  { rewrite app_nil_r. eauto. }
  iApply (step_fupdN_fresh_wand with "H").
  iIntros (???) "H".
  iApply (step_fupdN_wand with "H"); auto.
  iIntros "H".
  iDestruct "H" as (v2 ???) "(Hw&Hv&Hnstuck&HNC)".
  destruct stat.
  - iDestruct "Hv" as "(Hv&#Hinv)".
    rewrite ?ncfupd_eq /ncfupd_def.
    iMod ("Hinv" with "[$] [$]") as "(Hp&HNC)".
    iDestruct "Hp" as %?.
    do 8 iModIntro.
    iSplit; [| iSplit]; eauto.
    iIntros (v2' ? Heq). subst. inversion Heq; subst.
    rewrite to_of_val. naive_solver.
  - iDestruct "Hv" as "(Heq1&Hv)".
    iDestruct "Heq1" as %(?&?&?); subst.
    rewrite ?ncfupd_eq /ncfupd_def.
    iMod ("Hinv1" with "[$] [$]") as "(Hp&HNC)".
    iDestruct "Hp" as %?.
    do 8 iModIntro.
    iSplit; [| iSplit]; eauto.
    iIntros (v2' ? Heq). subst. inversion Heq; subst.
    rewrite to_of_val. naive_solver.
Qed.
