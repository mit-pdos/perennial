From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export staged_invariant crash_lang recovery_weakestpre.
From Perennial.program_logic Require Import crash_adequacy.
Import uPred.

Set Default Proof Using "Type".

Section recovery_adequacy.
Context `{!perennialG Λ CS T Σ}.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φinv : invG Σ → pbundleG T Σ → iProp Σ.
Implicit Types Φc : invG Σ → pbundleG T Σ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Notation wptp s k t := ([∗ list] ef ∈ t, WPC ef @ s; k; ⊤; ∅ {{ fork_post }} {{ True }})%I.

Fixpoint step_fupdN_fresh k (ns: list nat) Hi0 (Hc0: crashG Σ) t0
         (P: invG Σ → crashG Σ → pbundleG T Σ → iProp Σ) {struct ns} :=
  match ns with
  | [] => P Hi0 Hc0 t0
  | (n :: ns) =>
    (|={⊤, ⊤}_k=>^(S (S n)) |={⊤, ∅}_k=> ▷
     ∀ Hi' Hc', NC ={⊤}=∗ (∃ t' : pbundleG T Σ, step_fupdN_fresh k ns Hi' Hc' t' P))%I
  end.

Lemma step_fupdN_fresh_snoc k (ns: list nat) n Hi0 Hc0 t0 Q:
  step_fupdN_fresh k (ns ++ [n]) Hi0 Hc0 t0 Q ≡
  step_fupdN_fresh k (ns) Hi0 Hc0 t0
    (λ Hi Hc' _, |={⊤, ⊤}_k=>^(S (S n)) |={⊤, ∅}_k=> ▷ ∀ Hi' Hc', NC ={⊤}=∗ ∃ t', Q Hi' Hc' t')%I.
Proof.
  apply (anti_symm (⊢)%I).
  - revert Hi0 Hc0 t0 Q.
    induction ns => ????; first by auto.
    iIntros "H".
    iApply (step_fupdN_innerN_wand ⊤ ⊤ k k with "[H] []"); auto.
    iIntros "H".
    iApply (step_fupdN_inner_wand' with "H"); auto.
    iIntros "H".
    iNext. iIntros (??) "HNC".
    iMod ("H" $! _ _ with "[$]") as (?) "H".
    iExists _. by iApply IHns.
  - revert Hi0 Hc0 t0 Q.
    induction ns => ???? //=.
    do 1 f_equiv.
    apply step_fupdN_mono. apply fupd_mono.
    iIntros "H".
    iApply (step_fupdN_inner_wand with "H"); auto.
    iIntros "H".
    iApply (step_fupdN_innerN_wand with "H"); auto.
    iIntros "H".
    iApply (step_fupdN_inner_wand' with "H"); auto.
    iIntros "H".
    iNext. iIntros (??) "HNC".
    iMod ("H" $! _ _ with "[$]") as (?) "H".
    iExists _. by iApply IHns.
Qed.

Lemma step_fupdN_fresh_pattern_wand {H: invG Σ} k n (Q Q': iProp Σ):
  (|={⊤, ⊤}_k=>^(S n) |={⊤, ∅}_k=> ▷ Q) -∗ (Q -∗ Q') -∗
  (|={⊤, ⊤}_k=>^(S n) |={⊤, ∅}_k=> ▷ Q').
Proof.
  iIntros "H Hwand". simpl.
  iApply (step_fupdN_wand with "H").
  iIntros "H". iMod "H". iModIntro.
  iApply (step_fupdN_innerN_wand with "H"); auto.
  iIntros "H".
  iApply (step_fupdN_inner_wand' with "H"); auto.
  iIntros "H".
  iNext.
  by iApply "Hwand".
Qed.

Lemma step_fupdN_fresh_pattern_plain {H: invG Σ} n (Q: iProp Σ) `{!Plain Q}:
  (|={⊤, ∅}▷=>^(S n) |={⊤, ∅}=> ▷ Q) -∗
  (|={⊤}=> ▷^(S (S n)) Q).
Proof.
  iIntros "H".
  iDestruct (step_fupdN_wand with "H []") as "H".
  { iApply fupd_plain_mask_empty. }
  rewrite -step_fupdN_S_fupd.
  iDestruct (step_fupdN_plain with "H") as "H".
  iMod "H". iModIntro. iNext. rewrite -later_laterN laterN_later. iNext. by iMod "H".
Qed.

Lemma step_fupdN_fresh_pattern_plain' {H: invG Σ} k n (Q: iProp Σ) `{!Plain Q}:
  (|={⊤, ⊤}_k=>^(S n) |={⊤, ∅}_k=> ▷ Q) -∗
  (|={⊤}=> ▷^(S (S n) * (S (S k))) Q).
Proof.
  iIntros "H".
  iDestruct (step_fupdN_innerN_wand with "H []") as "H"; auto.
  { iApply step_fupdN_inner_plain. }
  rewrite step_fupdN_innerN_S_fupd.
  iMod (step_fupdN_innerN_plain with "H") as "H".
  iModIntro.
  replace (S (S n) * (S (S k))) with (S n * (S (S k)) + S (S k)) by lia.
  rewrite laterN_plus. iApply (laterN_le (S n * S k)); first by lia.
  iNext. rewrite -laterN_later => //=.
Qed.

Lemma step_fupdN_fresh_wand k (ns: list nat) Hi0 Hc0 t0 Q Q':
  step_fupdN_fresh k (ns) Hi0 Hc0 t0 Q -∗ (∀ Hinv Hc t, Q Hinv Hc t -∗ Q' Hinv Hc t)
  -∗ step_fupdN_fresh k ns Hi0 Hc0 t0 Q'.
Proof.
  revert Hi0 Hc0 t0.
  induction ns => ???.
  - iIntros "H Hwand". iApply "Hwand". eauto.
  - iIntros "H Hwand". rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    iApply (step_fupdN_fresh_pattern_wand with "H [Hwand]").
    iIntros "H".
    iIntros (Hi' Hc') "HNC". iSpecialize ("H" $! Hi' Hc' with "[$]"). iMod "H" as (?) "H".
    iExists _. iApply (IHns with "H"). eauto.
Qed.

Fixpoint fresh_later_count k (ns: list nat) :=
  match ns with
  | [] => (S (S k))
  | n :: ns' => (S (S (S n)) * (S (S k))) + fresh_later_count k ns'
  end.

Lemma step_fupdN_fresh_plain `{!invPreG Σ} `{!crashPreG Σ} P `{!Plain P} k ns n:
  (∀ Hinv' Hc', NC -∗ |={⊤}=> ∃ t, step_fupdN_fresh k ns Hinv' Hc' t
                  (λ _ _ _, |={⊤, ⊤}_k=>^(S n) |={⊤, ∅}=> P)) -∗
  ▷^(fresh_later_count k ns + S (S k + S n * (S (S k)))) P.
Proof.
  iIntros "H".
  iInduction ns as [| n' ns] "IH".
  - rewrite /step_fupdN_fresh.
    iApply (bupd_plain (▷^(_) P)%I); try (iPureIntro; apply _).
    iMod wsat_alloc as (Hinv) "(Hw&HE)".
    iMod NC_alloc as (Hc) "HNC".
    iSpecialize ("H" $! Hinv Hc with "HNC").
    rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
    iMod ("H" with "[$]") as "[>Hw [>HE >H]]".
    iDestruct ("H") as (_) "H".
    iDestruct (step_fupdN_fresh_pattern_plain' _ _ (P)%I with "[H]") as "H".
    iApply (step_fupdN_innerN_wand with "H"); try reflexivity.
    { iIntros "H". iMod "H". iApply step_fupdN_inner_later; auto. }
    rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
    iMod ("H" with "[$]") as "[Hw [HE >$]]"; eauto.
  - iMod wsat_alloc as (Hinv) "(Hw&HE)".
    iMod NC_alloc as (Hc) "HNC".
    iSpecialize ("H" $! Hinv).
    rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
    iMod ("H" with "HNC [$]") as "[>Hw [>HE >H]]".
    iDestruct "H" as (t) "H".
    rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    iDestruct (step_fupdN_fresh_pattern_wand  _ _ _
                  (▷^(fresh_later_count k ns + _) P)
                 with "H [IH]") as "H".
    { iIntros "H". iApply "IH". iIntros. by iMod ("H" with "[$]"). }
    iDestruct (step_fupdN_fresh_pattern_plain' with "H") as "H".
    rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
    iMod ("H" with "[$]") as "[Hw [HE >H]]".
    simpl. rewrite ?laterN_plus. iApply "H".
Qed.

(* XXX this probably needs to be tweaked. *)
Lemma step_fupdN_fresh_soundness `{!invPreG Σ} `{!crashPreG Σ} (φ : Prop) k ns n:
  (∀ (Hinv : invG Σ) (Hc: crashG Σ), NC -∗ (|={⊤}=> (∃ t0, step_fupdN_fresh k ns Hinv Hc t0
                             (λ _ _ _, |={⊤, ⊤}_k=>^(S (S n)) |={⊤, ∅}=> ▷ ⌜φ⌝)))%I) →
  φ.
Proof.
  intros Hiter.
  eapply (soundness (M:=iResUR Σ) _  (fresh_later_count k ns + _ + 1)); simpl.
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
  wptp s k t1 -∗ NC -∗ step_fupdN_fresh (3 * (S (S k))) ns Hi Hc t (λ Hi' Hc' t',
    ⌜ Hi' = Hi ∧ Hc' = Hc ∧ t' = t ⌝ ∗
    (|={⊤, ⊤}_(3 * (S (S k)))=>^(S n) ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC)).
Proof.
  iIntros (Hstep) "Hσ He Ht HNC".
  inversion Hstep. subst.
  iPoseProof (wptp_strong_adequacy with "Hσ [He] Ht HNC") as "H".
  { eauto. }
  {rewrite wpr_unfold /wpr_pre. iApply "He". }
  assert (ns = []) as ->;
    first by (eapply nrsteps_normal_empty_prefix; eauto).
  inversion H. subst.
  rewrite /step_fupdN_fresh.
  rewrite perennial_invG.
  iSplitL ""; first by eauto.
  iApply (step_fupdN_innerN_wand with "H"); auto.
Qed.

Lemma wptp_recv_strong_crash_adequacy Φ Φinv Φinv' Φr κs' s k Hi Hc t ns n r1 e1 t1 κs t2 σ1 σ2 :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, σ1) κs (t2, σ2) Crashed →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  wpr s k Hi Hc t ⊤ e1 r1 Φ Φinv Φr -∗
  □ (∀ Hi' t', Φinv Hi' t' -∗ □ Φinv' Hi' t') -∗
  wptp s k t1 -∗ NC -∗ step_fupdN_fresh (3 * (S (S k))) ns Hi Hc t (λ Hi' Hc' t',
    (|={⊤, ⊤}_(3 * (S (S k)))=>^(S (S n)) ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    from_option (Φr Hi' t') True (to_val e2) ∗
    □ Φinv' Hi' t' ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC)).
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
  iApply (step_fupdN_innerN_wand with "[-]"); try reflexivity.
  { rewrite -assoc wpr_unfold /wpr_pre.
    iPoseProof (@wptp_strong_crash_adequacy with "[$] [$] [$] [$]") as "H"; eauto.
    iEval (rewrite Nat_iter_S_r).
    rewrite perennial_invG.
    iApply (step_fupdN_innerN_wand ⊤ ⊤ (3 * (S (S k))) _ (S n') (S n') with "H"); auto.
    iIntros "H".
    iApply (step_fupdN_inner_wand with "H"); auto.
    { lia. }
    iIntros "H". iApply "H".
  }
  iIntros "H".
  rewrite -step_fupdN_inner_fupd.
  iApply (step_fupdN_inner_wand' with "H").
  { reflexivity. }
  { reflexivity. }
  { lia. }
  iIntros "H".
  iDestruct "H" as (e2 t2' ?) "(H&Hσ&HC)".
  iMod ("H" with "[//] Hσ") as "H". iModIntro. iNext.
  destruct s0.
  - iIntros (Hi' Hc') "HNC". iSpecialize ("H" $! Hi' Hc' with "[$]").
    iMod "H" as (t') "(Hσ&Hr&HNC)".
    iDestruct "Hr" as "(_&Hr)".
    iPoseProof (IH with "[Hσ] Hr [] [] HNC") as "H"; eauto.
  - iIntros (Hi' Hc') "HNC".
    iMod ("H" $! Hi' Hc' with "[$]") as (t') "(Hσ&Hr&HNC)".
    iExists t'.
    iAssert (□Φinv' Hi' t')%I as "#Hinv'".
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
    iApply (step_fupdN_innerN_wand with "H"); auto.
    iFrame "Hinv'". eauto.
Qed.

Lemma wptp_recv_strong_adequacy Φ Φinv Φinv' Φr κs' s k Hi Hc t ns n r1 e1 t1 κs t2 σ1 σ2 stat :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, σ1) κs (t2, σ2) stat →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  wpr s k Hi Hc t ⊤ e1 r1 Φ Φinv Φr -∗
  □ (∀ Hi' t', Φinv Hi' t' -∗ □ Φinv' Hi' t') -∗
  wptp s k t1 -∗ NC -∗ step_fupdN_fresh (3 * (S (S k))) ns Hi Hc t (λ Hi' Hc' t',
    (|={⊤, ⊤}_(3 * (S (S k)))=>^(S (S n)) ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    (match stat with
     | Normal => ⌜ Hi' = Hi ∧ t' = t ⌝ ∗ from_option Φ True (to_val e2)
     | Crashed => from_option (Φr Hi' t') True (to_val e2) ∗ □ Φinv' Hi' t'
     end)  ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC)).
Proof.
  intros. destruct stat.
  - iIntros. iDestruct (wptp_recv_strong_crash_adequacy with "[$] [$] [$] [$] [$]") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H").
    iIntros (???) "H".
    iApply (step_fupdN_innerN_wand with "H"); auto.
    iIntros "H".
    iDestruct "H" as (????) "(H&?&?&?)". iExists _, _.
    repeat (iSplitL ""; try iFrame; eauto).
  - iIntros. iDestruct (wptp_recv_strong_normal_adequacy with "[$] [$] [$] [$]") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H").
    iIntros (???) "H".
    iDestruct "H" as ((?&?&?)) "H". subst.
    iApply (step_fupdN_innerN_wand with "H"); auto.
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
     (|={⊤}=> ∃ (t: pbundleG T Σ)
         (stateI : pbundleG T Σ→ state Λ → list (observation Λ) → iProp Σ)
         (fork_post : pbundleG T Σ → val Λ → iProp Σ) Hpf,
        let _ : perennialG Λ CS _ Σ :=
            PerennialG _ _ T Σ
              (λ Hi t,
               IrisG Λ Σ Hi (λ σ κs _, stateI t σ κs)
                    (fork_post t)) Hpf
               in
       □ (∀ σ κ, stateI t σ κ ={⊤, ∅}=∗ ⌜ φinv σ ⌝) ∗
       □ (∀ Hi t, Φinv Hi t -∗ □ ∀ σ κ, stateI t σ κ ={⊤, ∅}=∗ ⌜ φinv σ ⌝) ∗
       stateI t σ κs ∗ wpr s k Hinv Hc t ⊤ e r (λ v, ⌜φ v⌝) Φinv (λ _ _ v, ⌜φr v⌝))%I) →
  recv_adequate (CS := CS) s e r σ (λ v _, φ v) (λ v _, φr v) φinv.
Proof.
  intros Hwp.
  apply recv_adequate_alt.
  intros t2 σ2 stat [n [κs H]]%erased_rsteps_nrsteps.
  destruct (nrsteps_snoc _ _ _ _ _ _ H) as (ns'&n'&->).
  eapply (step_fupdN_fresh_soundness _ (3 * (S (S k))) ns' n')=> Hinv Hc.
  iIntros "HNC".
  iMod (Hwp Hinv Hc κs) as (t stateI Hfork_post Hpf) "(#Hinv1&#Hinv2&Hw&H)".
  iModIntro. iExists _.
  iDestruct (wptp_recv_strong_adequacy
               (perennialG0 :=
          PerennialG _ _ T Σ
            (λ Hi t,
             IrisG Λ Σ Hi (λ σ κs _, stateI t σ κs)
                  (Hfork_post t)) Hpf) _ _ (λ _ t, (∀ σ κ, stateI t σ κ ={⊤, ∅}=∗ ⌜ φinv σ ⌝))%I
               _ [] with "[Hw] [H] [] [] HNC") as "H"; eauto.
  { rewrite app_nil_r. eauto. }
  iApply (step_fupdN_fresh_wand with "H").
  iIntros (???) "H".
  iApply (step_fupdN_innerN_wand with "H"); auto.
  iIntros "H".
  iDestruct "H" as (v2 ???) "(Hw&Hv&Hnstuck)".
  destruct stat.
  - iDestruct "Hv" as "(Hv&#Hinv)".
    iMod ("Hinv" with "[$]") as %?.
    iIntros "!> !>".
    iSplit; [| iSplit]; eauto.
    iIntros (v2' ? Heq). subst. inversion Heq; subst.
    rewrite to_of_val. naive_solver.
  - iDestruct "Hv" as "(Heq1&Hv)".
    iDestruct "Heq1" as %(?&?); subst.
    iMod ("Hinv1" with "[$]") as %?.
    iIntros "!> !>".
    iSplit; [| iSplit]; eauto.
    iIntros (v2' ? Heq). subst. inversion Heq; subst.
    rewrite to_of_val. naive_solver.
Qed.
