From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang crash_weakestpre.
Import uPred.

Section crash_adequacy.
Context `{!irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation wptp s k t := ([∗ list] ef ∈ t, WPC ef @ s; k; ⊤; ∅ {{ fork_post }} {{ True }})%I.

Lemma wpc_step s k e1 σ1 κ κs e2 σ2 efs m Φ Φc :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 (κ ++ κs) m -∗ WPC e1 @ s; k; ⊤; ∅ {{ Φ }} {{ Φc }} -∗
  |={⊤,⊤}_(2 * (S (S k)))=>
  state_interp σ2 κs (length efs + m) ∗
  WPC e2 @ s; k; ⊤; ∅ {{ Φ }} {{ Φc }} ∗
  wptp s k efs.
Proof.
  rewrite {1}wpc_unfold /wpc_pre. iIntros (?) "Hσ H".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iDestruct "H" as "(H&_)".
  replace (2 * S (S k)) with (S (S k) + S (S k)) by lia.
  rewrite Nat_iter_add Nat_iter_S.
  iMod ("H" $! σ1 with "Hσ") as "H".
  do 4 iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "(H&_)". rewrite Nat_iter_S.
  iMod "H" as "(_ & H)".
  iMod ("H" $! e2 σ2 efs with "[//]") as "H".
  iIntros "!> !>". by iMod "H".
Qed.

Lemma wptp_step s k e1 t1 t2 κ κs σ1 σ2 Φ Φc :
  step (e1 :: t1,σ1) κ (t2, σ2) →
  state_interp σ1 (κ ++ κs) (length t1) -∗ WPC e1 @ s; k; ⊤; ∅ {{ Φ }} {{ Φc }}-∗ wptp s k t1 ==∗
  ∃ e2 t2', ⌜t2 = e2 :: t2'⌝ ∗
  |={⊤,⊤}_(2 * (S (S k)))=> state_interp σ2 κs (pred (length t2)) ∗ WPC e2 @ s; k; ⊤; ∅ {{ Φ }} {{ Φc}} ∗ wptp s k t2'.
Proof.
  iIntros (Hstep) "Hσ He Ht".
  destruct Hstep as [e1' σ1' e2' σ2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', (t2' ++ efs). iModIntro. iSplitR; first by eauto.
    iMod (wpc_step with "Hσ He") as "H"; first done.
    iApply (step_fupdN_wand with "H"). iModIntro. iIntros "H".
    iMod "H" as "(Hσ & He2 & Hefs)".
    iIntros "!>". rewrite Nat.add_comm app_length. iFrame.
  - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
    iDestruct "Ht" as "(Ht1 & He1 & Ht2)".
    iModIntro. iMod (wpc_step with "Hσ He1") as "H"; first done.
    iApply (step_fupdN_wand with "H"). iModIntro. iIntros "H".
    iMod "H" as "(Hσ & He2 & Hefs)". iIntros "!>".
    iFrame "He". rewrite !app_length /= !app_length.
    replace (length t1' + S (length t2' + length efs))
      with (length efs + (length t1' + S (length t2'))) by omega. iFrame.
Qed.

Lemma wptp_steps s k n e1 t1 κs κs' t2 σ1 σ2 Φ Φc :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗ WPC e1 @ s; k; ⊤; ∅ {{ Φ }} {{ Φc }} -∗ wptp s k t1 -∗
  |={⊤,⊤}_(2 * (S (S k)))=>^n (∃ e2 t2',
    ⌜t2 = e2 :: t2'⌝ ∗
    state_interp σ2 κs' (pred (length t2)) ∗
    WPC e2 @ s; k; ⊤; ∅ {{ Φ }} {{ Φc }} ∗ wptp s k t2').
Proof.
  revert e1 t1 κs κs' t2 σ1 σ2; simpl.
  induction n as [|n IH]=> e1 t1 κs κs' t2 σ1 σ2 /=.
  { inversion_clear 1; iIntros "???"; iExists e1, t1; iFrame; eauto 10. }
  iIntros (Hsteps) "Hσ He Ht". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite -(assoc_L (++)).
  iMod (wptp_step with "Hσ He Ht") as (e1' t1'' ?) ">H"; first eauto; simplify_eq.
  iApply (step_fupdN_wand with "H"). iModIntro. iIntros "H".
  iMod "H" as "(Hσ & He & Ht)". iIntros "!>".
  by iApply (IH with "Hσ He Ht").
Qed.

Lemma wpc_safe k κs m e σ Φ Φc :
  state_interp σ κs m -∗
  WPC e @ k {{ Φ }} {{ Φc }} ={⊤}=∗ ▷^(S (S k))
  ⌜is_Some (to_val e) ∨ reducible e σ⌝.
Proof.
  rewrite wpc_unfold /wpc_pre. iIntros "Hσ (H&_)".
  destruct (to_val e) as [v|] eqn:?; first by eauto.
  iSpecialize ("H" $! σ [] κs with "Hσ").
  iMod (step_fupdN_inner_plain with "[H]") as "H".
  2: { iMod "H". iApply (step_fupdN_wand with "H").
       iModIntro. iIntros "(H&_)". iMod "H" as "(H&_)".
       iApply "H". }
  { apply _. }
  iModIntro; eauto.
  repeat iNext; iDestruct "H" as %?; eauto.
Qed.

Lemma wptp_strong_adequacy Φ Φc k κs' s n e1 t1 κs t2 σ1 σ2 :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WPC e1 @ s; k; ⊤; ∅ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗ |={⊤,⊤}_(2 * (S (S k)))=>^(S n) (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v)).
Proof.
  iIntros (Hstep) "Hσ He Ht". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps with "Hσ He Ht") as "Hwp"; first done.
  iApply (step_fupdN_innerN_wand with "Hwp"); auto.
  iDestruct 1 as (e2' t2' ?) "(Hσ & Hwp & Ht)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    (▷^(S (S k)) ⌜ ∀ e2, s = NotStuck → e2 ∈ (e2' :: t2') → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝)%I
    (state_interp σ2 κs' (length t2') ∗ WPC e2' @ s; k; ⊤; ∅ {{ v, Φ v }} {{ Φc }} ∗ wptp s k t2')%I
    with "[$Hσ $Hwp $Ht]") as "(Hsafe&Hσ&Hwp&Hvs)".
  { iIntros "(Hσ & Hwp & Ht)" (e' -> He').
    apply elem_of_cons in He' as [<-|(t1''&t2''&->)%elem_of_list_split].
    - iMod (wpc_safe with "Hσ Hwp") as "$"; auto.
    - iDestruct "Ht" as "(_ & He' & _)". by iMod (wpc_safe with "Hσ He'"). }
  iApply step_fupd_fupd. iApply step_fupd_intro; first done.
  iMod (fupd_intro_mask' _ ∅) as "Hclo". auto.
  do 5 (iModIntro). iMod "Hclo".
  iApply step_fupdN_inner_fupd.
  iApply (step_fupdN_inner_later); auto.
  iNext.
  iExists _, _. iSplitL ""; first done. iFrame "Hsafe Hσ".
  iSplitL "Hwp".
  - destruct (to_val e2') as [v2|] eqn:He2'; last done.
    apply of_to_val in He2' as <-. iApply (wpc_value_inv' with "Hwp").
  - clear Hstep. iInduction t2' as [|e t2'] "IH"; csimpl; first by iFrame.
    iDestruct "Hvs" as "[Hv Hvs]". destruct (to_val e) as [v|] eqn:He.
    + apply of_to_val in He as <-. iMod (wpc_value_inv' with "Hv") as "$".
      by iApply ("IH" with "[$]").
    + by iApply ("IH" with "[$]").
Qed.

Lemma wptp_strong_crash_adequacy Φ Φc κs' s k n e1 t1 κs t2 σ1 σ2 :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WPC e1 @ s; k; ⊤; ∅ {{ Φ }} {{ Φc }} -∗
  wptp s k t1 -∗ |={⊤,⊤}_(2 * S (S k))=>^(S n) |={⊤, ∅}_(S k)=> (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    Φc ∗ state_interp σ2 κs' (length t2')).
Proof.
  iIntros (Hstep) "Hσ He Ht". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps with "Hσ He Ht") as "Hwp"; first done.
  iApply (step_fupdN_innerN_wand with "Hwp"); auto.
  iDestruct 1 as (e2' t2' ?) "(Hσ & Hwp & Ht)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    (▷^(S (S k)) ⌜ ∀ e2, s = NotStuck → e2 ∈ (e2' :: t2') → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝)%I
    (state_interp σ2 κs' (length t2') ∗ WPC e2' @ s; k; ⊤; ∅ {{ v, Φ v }} {{ Φc }} ∗ wptp s k t2')%I
    with "[$Hσ $Hwp $Ht]") as "(Hsafe&Hσ&Hwp&Hvs)".
  { iIntros "(Hσ & Hwp & Ht)" (e' -> He').
    apply elem_of_cons in He' as [<-|(t1''&t2''&->)%elem_of_list_split].
    - iMod (wpc_safe with "Hσ Hwp") as "$"; auto.
    - iDestruct "Ht" as "(_ & He' & _)". by iMod (wpc_safe with "Hσ He'"). }
  iApply step_fupd_fupd. iApply step_fupd_intro; first done.
  iMod (fupd_intro_mask' _ ∅) as "Hclo". auto.
  do 5 (iModIntro). iMod "Hclo".
  iApply step_fupdN_inner_fupd.
  iApply (step_fupdN_inner_later); auto.
  iNext. iModIntro.
  iMod (wpc_crash with "Hwp") as "H".
  iApply (step_fupdN_inner_wand _ _ (S k) with "H [-]"); eauto.
  iIntros "($&?)". iExists _, _; eauto.
Qed.
End crash_adequacy.

(*** Recovery ***)

Class pbundleG (T: ofeT) (Σ: gFunctors) := {
  pbundleT : T
}.

Class perennialG (Λ : language) (CS: crash_semantics Λ) (T: ofeT) (Σ : gFunctors) := PerennialG {
  perennial_irisG :> ∀ H, pbundleG T Σ → irisG Λ Σ;
  perennial_invG: ∀ H t, @iris_invG _ _ (perennial_irisG H t) = H
}.

Definition wpr_pre `{perennialG Λ CS T Σ} (s : stuckness) (k: nat)
    (wpr : invG Σ -d> pbundleG T Σ -d> coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d>
                     (invG Σ -d> pbundleG T Σ -d> val Λ -d> iPropO Σ) -d> iPropO Σ) :
  invG Σ -d> pbundleG T Σ -d> coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> (invG Σ -d> pbundleG T Σ -d> val Λ -d> iPropO Σ) -d> iPropO Σ :=
  λ H t E e rec Φ Φr,
  (WPC e @ s ; k; E ; ∅
     {{ Φ }}
     {{ ∀ σ σ' (HC: crash_prim_step CS σ σ') κs n,
        state_interp σ κs n ={∅}=∗  ▷ ∀ H, ∃ t, state_interp σ' κs 0 ∗ wpr H t E rec rec (λ v, Φr H t v) Φr}})%I.

Local Instance wpr_pre_contractive `{!perennialG Λ CS T Σ} s k: Contractive (wpr_pre s k).
Proof.
  rewrite /wpr_pre=> n wp wp' Hwp ? t E1 e1 rec Φ Φc.
  apply wpc_ne; eauto;
  repeat (f_contractive || f_equiv). apply Hwp.
Qed.

Definition wpr_def `{!perennialG Λ CS T Σ} (s : stuckness) k :
  invG Σ → pbundleG T Σ → coPset → expr Λ → expr Λ → (val Λ → iProp Σ) → (invG Σ → pbundleG T Σ → val Λ → iProp Σ) → iProp Σ := fixpoint (wpr_pre s k).
Definition wpr_aux `{!perennialG Λ CS T Σ} : seal (@wpr_def Λ CS T Σ _). by eexists. Qed.
Definition wpr `{!perennialG Λ CS T Σ} := wpr_aux.(unseal).
Definition wpr_eq `{!perennialG Λ CS T Σ} : wpr = @wpr_def Λ CS T Σ _ := wpr_aux.(seal_eq).

Section wpr.
Context `{!perennialG Λ CS T Σ}.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : invG Σ → pbundleG T Σ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma wpr_unfold s k Hi t E e rec Φ Φc :
  wpr s k Hi t E e rec Φ Φc ⊣⊢ wpr_pre s k (wpr s k) Hi t E e rec Φ Φc.
Proof. rewrite wpr_eq. apply (fixpoint_unfold (wpr_pre s k)). Qed.

(* There's a stronger version of this *)
Lemma wpr_strong_mono s k Hi t E e rec Φ Ψ Φr Ψr :
  wpr s k Hi t E e rec Φ Φr -∗
  (∀ v, Φ v ==∗ Ψ v) ∧ (∀ Hi t v, Φr Hi t v ==∗ Ψr Hi t v) -∗
  wpr s k Hi t E e rec Ψ Ψr.
Proof.
  iIntros "H HΦ". iLöb as "IH" forall (e t Hi E Φ Ψ Φr Ψr).
  rewrite ?wpr_unfold /wpr_pre.
  iApply (wpc_strong_mono with "H") ; auto.
  iSplit.
  { iDestruct "HΦ" as "(H&_)". iIntros. iMod ("H" with "[$]"); eauto. }
  iIntros "H".
  iModIntro. iIntros (?????) "Hinterp". iMod ("H" with "[//] Hinterp") as "H".
  iModIntro. iNext. iIntros (Hi'). iDestruct ("H" $! Hi') as (?) "(?&H)".
  iExists _. iFrame. iApply ("IH" with "[$]").
  iSplit; iIntros; iDestruct ("HΦ") as "(_&H)"; by iMod ("H" with "[$]").
Qed.

(* To prove a recovery wp for e with rec, it suffices to prove a crash wp for e,
   where the crash condition implies the precondition for a crash wp for rec *)
Lemma idempotence_wpr s k E e rec Φx Φrx Φcx Hi t:
  ((WPC e @ s ; k ; E ; ∅ {{ Φx t }} {{ Φcx t }}) -∗
   (□ ∀ (H: invG Σ) (t: pbundleG T Σ) σ σ' (HC: crash_prim_step CS σ σ') κs n,
        Φcx t -∗ state_interp σ κs n ={∅}=∗
        ▷ ∀ H', ∃ t', state_interp σ' κs 0 ∗ WPC rec @ s ; k; E ; ∅ {{ Φrx H' t' }} {{ Φcx t' }}) -∗
    wpr s k Hi t E e rec (Φx t) Φrx)%I.
Proof.
  iLöb as "IH" forall (E e Hi t Φx).
  iIntros "He #Hidemp".
  rewrite wpr_unfold. rewrite /wpr_pre.
  iApply (wpc_strong_mono with "He"); [ auto | auto | auto | auto | ].
  iSplit; first auto. iIntros "Hcx". iModIntro.
  iIntros. iMod ("Hidemp" with "[ ] [$] [$]") as "H".
  { eauto. }
  iModIntro. iNext. iIntros (Hi'). iDestruct ("H" $! Hi') as (t') "(?&Hc)".
  iExists _. iFrame.
  iApply ("IH" $! E rec Hi' t' (λ t v, Φrx Hi' t v)%I with "[Hc]").
  { iApply (wpc_strong_mono with "Hc"); auto. }
  eauto.
Qed.

End wpr.

Section recovery_adequacy.
Context `{!perennialG Λ CS T Σ}.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : invG Σ → pbundleG T Σ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Notation wptp s k t := ([∗ list] ef ∈ t, WPC ef @ s; k; ⊤; ∅ {{ fork_post }} {{ True }})%I.

Fixpoint step_fupdN_fresh k (ns: list nat) Hi0 t0 (P: invG Σ → pbundleG T Σ → iProp Σ) :=
  match ns with
  | [] => P Hi0 t0
  | (n :: ns) =>
    (|={⊤, ⊤}_k=>^(S n) |={⊤, ∅}_k=> ▷
     ∀ Hi', (∃ t' : pbundleG T Σ, step_fupdN_fresh k ns Hi' t' P))%I
  end.

Lemma step_fupdN_fresh_snoc k (ns: list nat) n Hi0 t0 Q:
  step_fupdN_fresh k (ns ++ [n]) Hi0 t0 Q ≡
  step_fupdN_fresh k (ns) Hi0 t0
    (λ Hi _, |={⊤, ⊤}_k=>^(S n) |={⊤, ∅}_k=> ▷ ∀ Hi', ∃ t', Q Hi' t')%I.
Proof.
  apply (anti_symm (⊢)%I).
  - revert Hi0 t0 Q.
    induction ns => ??? //=. do 1 f_equiv.
    apply step_fupdN_mono. apply fupd_mono.
    iIntros "H".
    iApply (step_fupdN_innerN_wand with "H"); auto.
    iIntros "H".
    iApply (step_fupdN_inner_wand' with "H"); auto.
    iIntros "H". iNext. iIntros.
    iDestruct ("H" $! _) as (?) "H".
    iExists _. by iApply IHns.
  - revert Hi0 t0 Q.
    induction ns => ??? //=. do 1 f_equiv.
    apply step_fupdN_mono. apply fupd_mono.
    iIntros "H".
    iApply (step_fupdN_innerN_wand with "H"); auto.
    iIntros "H".
    iApply (step_fupdN_inner_wand' with "H"); auto.
    iIntros "H". iNext. iIntros.
    iDestruct ("H" $! _) as (?) "H".
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

Lemma step_fupdN_fresh_wand k (ns: list nat) Hi0 t0 Q Q':
  step_fupdN_fresh k (ns) Hi0 t0 Q -∗ (∀ Hinv t, Q Hinv t -∗ Q' Hinv t)
  -∗ step_fupdN_fresh k ns Hi0 t0 Q'.
Proof.
  revert Hi0 t0.
  induction ns => ??.
  - iIntros "H Hwand". iApply "Hwand". eauto.
  - iIntros "H Hwand". simpl.
    iApply (step_fupdN_fresh_pattern_wand with "H [Hwand]").
    iIntros "H".
    iIntros (Hi'). iSpecialize ("H" $! Hi'). iDestruct "H" as (?) "H".
    iExists _. iApply (IHns with "H"). eauto.
Qed.

Fixpoint fresh_later_count k (ns: list nat) :=
  match ns with
  | [] => (S (S k))
  | n :: ns' => (S (S n) * (S (S k))) + fresh_later_count k ns'
  end.

Lemma step_fupdN_fresh_plain `{!invPreG Σ} P `{!Plain P} k ns n:
  (∀ Hinv', |={⊤}=> ∃ t, step_fupdN_fresh k ns Hinv' t
                  (λ _ _, |={⊤, ⊤}_k=>^(S n) |={⊤, ∅}=> P)) -∗
  ▷^(fresh_later_count k ns + S (S k + n * (S (S k)))) P.
Proof.
  iIntros "H".
  iInduction ns as [| n' ns] "IH".
  - rewrite /step_fupdN_fresh.
    iApply (bupd_plain (▷^(_) P)%I); try (iPureIntro; apply _).
    iMod wsat_alloc as (Hinv) "(Hw&HE)".
    iSpecialize ("H" $! Hinv).
    rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
    iMod ("H" with "[$]") as "[>Hw [>HE >H]]".
    iDestruct ("H") as (_) "H".
    iDestruct (step_fupdN_fresh_pattern_plain' _ _ (P)%I with "[H]") as "H".
    iApply (step_fupdN_innerN_wand with "H"); try reflexivity.
    { iIntros "H". iMod "H". iApply step_fupdN_inner_later; auto. }
    rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
    iMod ("H" with "[$]") as "[Hw [HE >$]]"; eauto.
  - iMod wsat_alloc as (Hinv) "(Hw&HE)".
    iSpecialize ("H" $! Hinv).
    rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
    iMod ("H" with "[$]") as "[>Hw [>HE >H]]".
    iDestruct "H" as (t) "H".
    rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    iDestruct (step_fupdN_fresh_pattern_wand  _ _ _
                  (▷^(fresh_later_count k ns + _) P)
                 with "H [IH]") as "H".
    { iIntros "H". iApply "IH". iIntros. iModIntro. iApply "H". }
    iDestruct (step_fupdN_fresh_pattern_plain' with "H") as "H".
    rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
    iMod ("H" with "[$]") as "[Hw [HE >H]]".
    simpl. rewrite ?laterN_plus. iApply "H".
Qed.

(* XXX this probably needs to be tweaked. *)
Lemma step_fupdN_fresh_soundness `{!invPreG Σ} (φ : Prop) k ns n:
  (∀ Hinv : invG Σ, (|={⊤}=> (∃ t0, step_fupdN_fresh k ns Hinv t0
                             (λ _ _, |={⊤, ⊤}_k=>^(S n) |={⊤, ∅}=> ▷ ⌜φ⌝)))%I) →
  φ.
Proof.
  intros Hiter.
  eapply (soundness (M:=iResUR Σ) _  (fresh_later_count k ns + _ + 1)); simpl.
  rewrite laterN_plus.
  iApply step_fupdN_fresh_plain. iIntros (Hinv). iApply Hiter.
Qed.

(*
Notation "|={ E }=>_( t ) Q" := (fupd (FUpd := t) E E Q)
 (at level 99) : bi_scope.
Notation "P ={ E }=∗_ t Q" := (P -∗ |={E}=>_(t) Q)%I
 (at level 99) : bi_scope.
*)

Lemma wptp_recv_strong_normal_adequacy Φ Φr κs' s k Hi t n ns r1 e1 t1 κs t2 σ1 σ2 :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, σ1) κs (t2, σ2) Normal →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  wpr s k Hi t ⊤ e1 r1 Φ Φr -∗
  wptp s k t1 -∗ step_fupdN_fresh (2 * (S (S k))) ns Hi t (λ Hi' t',
    ⌜ Hi' = Hi ∧ t' = t ⌝ ∗
    (|={⊤, ⊤}_(2 * (S (S k)))=>^(S n) |={⊤, ∅}=> ▷ ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v))).
Proof.
  iIntros (Hstep) "Hσ He Ht".
  inversion Hstep. subst.
  iPoseProof (wptp_strong_adequacy with "Hσ [He] Ht") as "H".
  { eauto. }
  {rewrite wpr_unfold /wpr_pre. iApply "He". }
  assert (ns = []) as ->;
    first by (eapply nrsteps_normal_empty_prefix; eauto).
  inversion H. subst.
  rewrite /step_fupdN_fresh.
  rewrite perennial_invG.
  iSplitL ""; first by eauto.
  iApply (step_fupdN_innerN_wand with "H"); auto.
  iIntros. iApply fupd_mask_weaken; first by set_solver+.
  iNext. eauto.
Qed.

Lemma wptp_recv_strong_crash_adequacy Φ Φr κs' s k Hi t ns n r1 e1 t1 κs t2 σ1 σ2 :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, σ1) κs (t2, σ2) Crashed →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  wpr s k Hi t ⊤ e1 r1 Φ Φr -∗
  wptp s k t1 -∗ step_fupdN_fresh (2 * (S (S k))) ns Hi t (λ Hi' t',
    (|={⊤, ⊤}_(2 * (S (S k)))=>^(S n) |={⊤, ∅}=> ▷ ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    from_option (Φr Hi' t') True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v))).
Proof.
  revert Hi t e1 t1 κs κs' t2 σ1 σ2 Φ.
  induction ns as [|n' ns' IH] => Hi t e1 t1 κs κs' t2 σ1 σ2 Φ.
  { rewrite app_nil_l.
    inversion 1.
    match goal with
    | [ H : nrsteps _ _ _ _ _ _ |- _ ] => inversion H
    end.
  }
  iIntros (Hsteps) "Hσ He Ht".
  inversion_clear Hsteps as [|?? [t1' σ1'] ????? s0].
  rewrite {1}/step_fupdN_fresh -/step_fupdN_fresh.
  destruct ρ2 as (?&σ2_pre_crash).
  iApply (step_fupdN_innerN_wand with "[-]"); try reflexivity.
  { rewrite -assoc wpr_unfold /wpr_pre.
    iPoseProof (@wptp_strong_crash_adequacy with "[$] [$]") as "H"; eauto.
    rewrite perennial_invG. by iApply "H".
  }
  iIntros "H".
  rewrite -step_fupdN_inner_fupd.
  iApply (step_fupdN_inner_wand' with "H").
  { reflexivity. }
  { reflexivity. }
  { lia. }
  iIntros "H".
  iDestruct "H" as (e2 t2' ?) "(H&Hσ)".
  iMod ("H" with "[//] Hσ") as "H". iModIntro. iNext.
  destruct s0.
  - iIntros (Hi'). iSpecialize ("H" $! Hi').
    iDestruct "H" as (t') "(Hσ&Hr)".
    iPoseProof (IH with "[Hσ] Hr []") as "H"; eauto.
  - iIntros (Hi').
    iDestruct ("H" $! Hi') as (t') "(Hσ&Hr)".
    iExists t'.
    iDestruct (wptp_recv_strong_normal_adequacy with "[Hσ] [Hr] []") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H").
    iIntros (??) "H".
    iDestruct "H" as ((?&?)) "H". subst.
    iApply "H".
Qed.

Lemma wptp_recv_strong_adequacy Φ Φr κs' s k Hi t ns n r1 e1 t1 κs t2 σ1 σ2 stat :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, σ1) κs (t2, σ2) stat →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  wpr s k Hi t ⊤ e1 r1 Φ Φr -∗
  wptp s k t1 -∗ step_fupdN_fresh (2 * (S (S k))) ns Hi t (λ Hi' t',
    (|={⊤, ⊤}_(2 * (S (S k)))=>^(S n) |={⊤, ∅}=> ▷ ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    (match stat with
     | Normal => ⌜ Hi' = Hi ∧ t' = t ⌝ ∗ from_option Φ True (to_val e2)
     | Crashed => from_option (Φr Hi' t') True (to_val e2)
     end)  ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v))).
Proof.
  intros. destruct stat.
  - by iApply wptp_recv_strong_crash_adequacy.
  - iIntros. iDestruct (wptp_recv_strong_normal_adequacy with "[$] [$] [$]") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H").
    iIntros (??) "H".
    iDestruct "H" as ((?&?)) "H". subst.
    iApply (step_fupdN_innerN_wand with "H"); auto.
    iIntros ">H !> !> ".
    iDestruct "H" as (????) "(H&?&?)". iExists _, _.
    repeat (iSplitL ""; try iFrame; eauto).
Qed.

End recovery_adequacy.

Record recv_adequate {Λ CS} (s : stuckness) (e1 r1: expr Λ) (σ1 : state Λ)
    (φ φr: val Λ → state Λ → Prop) := {
  recv_adequate_result_normal t2 σ2 v2 :
   erased_rsteps (CS := CS) r1 ([e1], σ1) (of_val v2 :: t2, σ2) Normal →
   φ v2 σ2;
  recv_adequate_result_crashed t2 σ2 v2 :
   erased_rsteps (CS := CS) r1 ([e1], σ1) (of_val v2 :: t2, σ2) Crashed →
   φr v2 σ2;
  recv_adequate_not_stuck t2 σ2 e2 stat :
   s = NotStuck →
   erased_rsteps (CS := CS) r1 ([e1], σ1) (t2, σ2) stat →
   e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2)
}.

Lemma recv_adequate_alt {Λ CS} s e1 r1 σ1 (φ φr : val Λ → state Λ → Prop) :
  recv_adequate (CS := CS) s e1 r1 σ1 φ φr ↔ ∀ t2 σ2 stat,
    erased_rsteps (CS := CS) r1 ([e1], σ1) (t2, σ2) stat →
      (∀ v2 t2', t2 = of_val v2 :: t2' →
                 match stat with
                   | Normal => φ v2 σ2
                   | Crashed => φr v2 σ2
                 end) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2)).
Proof.
  split.
  - intros [] ?? []; naive_solver.
  - constructor; naive_solver.
Qed.

Corollary wp_recv_adequacy Σ Λ CS (T: ofeT) `{!invPreG Σ} s k e r σ φ φr :
  (∀ `{Hinv : !invG Σ} κs,
     (|={⊤}=> ∃ (t: pbundleG T Σ)
         (stateI : pbundleG T Σ→ state Λ → list (observation Λ) → iProp Σ)
         (fork_post : pbundleG T Σ → val Λ → iProp Σ) Hpf,
        let _ : perennialG Λ CS _ Σ :=
            PerennialG _ _ T Σ
              (λ Hi t,
               IrisG Λ Σ Hi (λ σ κs _, stateI t σ κs)
                    (fork_post t)) Hpf
               in
       stateI t σ κs ∗ wpr s k Hinv t ⊤ e r (λ v, ⌜φ v⌝) (λ _ _ v, ⌜φr v⌝))%I) →
  recv_adequate (CS := CS) s e r σ (λ v _, φ v) (λ v _, φr v) .
Proof.
  intros Hwp.
  apply recv_adequate_alt.
  intros t2 σ2 stat [n [κs H]]%erased_rsteps_nrsteps.
  destruct (nrsteps_snoc _ _ _ _ _ _ H) as (ns'&n'&->).
  eapply (step_fupdN_fresh_soundness _ (2 * (S (S k))) ns' n')=> Hinv.
  iMod (Hwp Hinv κs) as (t stateI Hfork_post Hpf) "(Hw&H)".
  iModIntro. iExists _.
  iDestruct (wptp_recv_strong_adequacy
               (perennialG0 :=
          PerennialG _ _ T Σ
            (λ Hi t,
             IrisG Λ Σ Hi (λ σ κs _, stateI t σ κs)
                  (Hfork_post t)) Hpf) _ _ [] with "[Hw] [H] []") as "H"; eauto.
  { rewrite app_nil_r. eauto. }
  iApply (step_fupdN_fresh_wand with "H").
  iIntros (??) "H".
  iApply (step_fupdN_innerN_wand with "H"); auto.
  iIntros ">H !> !> ".
  iDestruct "H" as (v2 ???) "(_&Hv&Hnstuck)".
  iSplitR ""; last done.
  iIntros (v2' ? Heq). subst. inversion Heq; subst.
  rewrite to_of_val. destruct stat; iDestruct "Hv" as %?; eauto.
  naive_solver.
Qed.
