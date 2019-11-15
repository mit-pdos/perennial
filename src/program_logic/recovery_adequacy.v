From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang crash_weakestpre.
Import uPred.

Section crash_adequacy.
Context `{!irisG Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation wptp s t := ([∗ list] ef ∈ t, WPC ef @ s; ⊤; ∅ {{ fork_post }} {{ True }})%I.

Lemma wpc_step s e1 σ1 κ κs e2 σ2 efs m Φ Φc :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 (κ ++ κs) m -∗ WPC e1 @ s; ⊤; ∅ {{ Φ }} {{ Φc }} ={⊤,∅}▷=∗
  state_interp σ2 κs (length efs + m) ∗
  WPC e2 @ s; ⊤; ∅ {{ Φ }} {{ Φc }} ∗
  wptp s efs.
Proof.
  rewrite {1}wpc_unfold /wpc_pre. iIntros (?) "Hσ H".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iDestruct "H" as "(H&_)".
  iMod ("H" $! σ1 with "Hσ") as "(_ & H)".
  iMod ("H" $! e2 σ2 efs with "[//]") as "H".
  by iIntros "!> !>".
Qed.

Lemma wptp_step s e1 t1 t2 κ κs σ1 σ2 Φ Φc :
  step (e1 :: t1,σ1) κ (t2, σ2) →
  state_interp σ1 (κ ++ κs) (length t1) -∗ WPC e1 @ s; ⊤; ∅ {{ Φ }} {{ Φc }}-∗ wptp s t1 ==∗
  ∃ e2 t2', ⌜t2 = e2 :: t2'⌝ ∗
  |={⊤,∅}▷=> state_interp σ2 κs (pred (length t2)) ∗ WPC e2 @ s; ⊤; ∅ {{ Φ }} {{ Φc}}  ∗ wptp s t2'.
Proof.
  iIntros (Hstep) "Hσ He Ht".
  destruct Hstep as [e1' σ1' e2' σ2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', (t2' ++ efs). iModIntro. iSplitR; first by eauto.
    iMod (wpc_step with "Hσ He") as "H"; first done.
    iIntros "!> !>". iMod "H" as "(Hσ & He2 & Hefs)".
    iIntros "!>". rewrite Nat.add_comm app_length. iFrame.
  - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
    iFrame "He". iDestruct "Ht" as "(Ht1 & He1 & Ht2)".
    iModIntro. iMod (wpc_step with "Hσ He1") as "H"; first done.
    iIntros "!> !>". iMod "H" as "(Hσ & He2 & Hefs)". iIntros "!>".
    rewrite !app_length /= !app_length.
    replace (length t1' + S (length t2' + length efs))
      with (length efs + (length t1' + S (length t2'))) by omega. iFrame.
Qed.

Lemma wptp_steps s n e1 t1 κs κs' t2 σ1 σ2 Φ Φc :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗ WPC e1 @ s; ⊤; ∅ {{ Φ }} {{ Φc }} -∗ wptp s t1
  ={⊤,∅}▷=∗^n ∃ e2 t2',
    ⌜t2 = e2 :: t2'⌝ ∗
    state_interp σ2 κs' (pred (length t2)) ∗
    WPC e2 @ s; ⊤; ∅ {{ Φ }} {{ Φc }} ∗ wptp s t2'.
Proof.
  revert e1 t1 κs κs' t2 σ1 σ2; simpl.
  induction n as [|n IH]=> e1 t1 κs κs' t2 σ1 σ2 /=.
  { inversion_clear 1; iIntros "???"; iExists e1, t1; iFrame; eauto 10. }
  iIntros (Hsteps) "Hσ He Ht". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite -(assoc_L (++)).
  iMod (wptp_step with "Hσ He Ht") as (e1' t1'' ?) ">H"; first eauto; simplify_eq.
  iIntros "!> !>". iMod "H" as "(Hσ & He & Ht)". iModIntro.
  by iApply (IH with "Hσ He Ht").
Qed.

Lemma wpc_safe κs m e σ Φ Φc :
  state_interp σ κs m -∗
  WPC e {{ Φ }} {{ Φc }} ={⊤}=∗ ⌜is_Some (to_val e) ∨ reducible e σ⌝.
Proof.
  rewrite wpc_unfold /wpc_pre. iIntros "Hσ (H&_)".
  destruct (to_val e) as [v|] eqn:?; first by eauto.
  iSpecialize ("H" $! σ [] κs with "Hσ"). rewrite sep_elim_l.
  iMod (fupd_plain_mask with "H") as %?; eauto.
Qed.

Lemma wptp_strong_adequacy Φ Φc κs' s n e1 t1 κs t2 σ1 σ2 :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WPC e1 @ s; ⊤; ∅ {{ Φ }} {{ Φc }} -∗
  wptp s t1 ={⊤,∅}▷=∗^(S n) (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v)).
Proof.
  iIntros (Hstep) "Hσ He Ht". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps with "Hσ He Ht") as "Hwp"; first done.
  iApply (step_fupdN_wand with "Hwp").
  iDestruct 1 as (e2' t2' ?) "(Hσ & Hwp & Ht)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    ⌜ ∀ e2, s = NotStuck → e2 ∈ (e2' :: t2') → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝%I
    (state_interp σ2 κs' (length t2') ∗ WPC e2' @ s; ⊤; ∅ {{ v, Φ v }} {{ Φc }} ∗ wptp s t2')%I
    with "[$Hσ $Hwp $Ht]") as "(Hsafe&Hσ&Hwp&Hvs)".
  { iIntros "(Hσ & Hwp & Ht)" (e' -> He').
    apply elem_of_cons in He' as [<-|(t1''&t2''&->)%elem_of_list_split].
    - iMod (wpc_safe with "Hσ Hwp") as "$"; auto.
    - iDestruct "Ht" as "(_ & He' & _)". by iMod (wpc_safe with "Hσ He'"). }
  iApply step_fupd_fupd. iApply step_fupd_intro; first done. iNext.
  iExists _, _. iSplitL ""; first done. iFrame "Hsafe Hσ".
  iSplitL "Hwp".
  - destruct (to_val e2') as [v2|] eqn:He2'; last done.
    apply of_to_val in He2' as <-. iApply (wpc_value_inv' with "Hwp").
  - clear Hstep. iInduction t2' as [|e t2'] "IH"; csimpl; first by iFrame.
    iDestruct "Hvs" as "[Hv Hvs]". destruct (to_val e) as [v|] eqn:He.
    + apply of_to_val in He as <-. iMod (wpc_value_inv' with "Hv") as "$".
      by iApply "IH".
    + by iApply "IH".
Qed.

Lemma wptp_strong_crash_adequacy Φ Φc κs' s n e1 t1 κs t2 σ1 σ2 :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WPC e1 @ s; ⊤; ∅ {{ Φ }} {{ Φc }} -∗
  wptp s t1 ={⊤,∅}▷=∗^(S n) |={⊤, ∅}=> (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    Φc ∗ state_interp σ2 κs' (length t2')).
Proof.
  iIntros (Hstep) "Hσ He Ht". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps with "Hσ He Ht") as "Hwp"; first done.
  iApply (step_fupdN_wand with "Hwp").
  iDestruct 1 as (e2' t2' ?) "(Hσ & Hwp & Ht)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    ⌜ ∀ e2, s = NotStuck → e2 ∈ (e2' :: t2') → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝%I
    (state_interp σ2 κs' (length t2') ∗ WPC e2' @ s; ⊤; ∅ {{ v, Φ v }} {{ Φc }} ∗ wptp s t2')%I
    with "[$Hσ $Hwp $Ht]") as "(Hsafe&Hσ&Hwp&Hvs)".
  { iIntros "(Hσ & Hwp & Ht)" (e' -> He').
    apply elem_of_cons in He' as [<-|(t1''&t2''&->)%elem_of_list_split].
    - iMod (wpc_safe with "Hσ Hwp") as "$"; auto.
    - iDestruct "Ht" as "(_ & He' & _)". by iMod (wpc_safe with "Hσ He'"). }
  iApply step_fupd_fupd. iApply step_fupd_intro; first done. iNext.
  iModIntro. iExists _, _.
  rewrite {1}wpc_unfold /wpc_pre.
  iDestruct "Hwp" as "(_&Hwp)".
  iMod ("Hwp" with "[$]") as "($&$)".
  iModIntro; eauto.
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

Definition wpr_pre `{perennialG Λ CS T Σ} (s : stuckness)
    (wpr : invG Σ -d> pbundleG T Σ -d> coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d>
                     (invG Σ -d> pbundleG T Σ -d> val Λ -d> iPropO Σ) -d> iPropO Σ) :
  invG Σ -d> pbundleG T Σ -d> coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> (invG Σ -d> pbundleG T Σ -d> val Λ -d> iPropO Σ) -d> iPropO Σ :=
  λ H t E e rec Φ Φr,
  (WPC e @ s ; E ; ∅
     {{ Φ }}
     {{ ∀ σ σ' (HC: crash_prim_step CS σ σ') κs n,
        state_interp σ κs n ={∅}=∗  ▷ ∀ H, ∃ t, state_interp σ' κs 0 ∗ wpr H t E rec rec (λ v, Φr H t v) Φr}})%I.

Local Instance wpr_pre_contractive `{!perennialG Λ CS T Σ} s : Contractive (wpr_pre s).
Proof.
  rewrite /wpr_pre=> n wp wp' Hwp ? t E1 e1 rec Φ Φc.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wpr_def `{!perennialG Λ CS T Σ} (s : stuckness) :
  invG Σ → pbundleG T Σ → coPset → expr Λ → expr Λ → (val Λ → iProp Σ) → (invG Σ → pbundleG T Σ → val Λ → iProp Σ) → iProp Σ := fixpoint (wpr_pre s).
Definition wpr_aux `{!perennialG Λ CS T Σ} : seal (@wpr_def Λ CS T Σ _). by eexists. Qed.
Definition wpr `{!perennialG Λ CS T Σ} := wpr_aux.(unseal).
Definition wpr_eq `{!perennialG Λ CS T Σ} : wpr = @wpr_def Λ CS T Σ _ := wpr_aux.(seal_eq).

Section wpr.
Context `{!perennialG Λ CS T Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : invG Σ → pbundleG T Σ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma wpr_unfold s Hi t E e rec Φ Φc :
  wpr s Hi t E e rec Φ Φc ⊣⊢ wpr_pre s (wpr s) Hi t E e rec Φ Φc.
Proof. rewrite wpr_eq. apply (fixpoint_unfold (wpr_pre s)). Qed.

(* There's a stronger version of this *)
Lemma wpr_strong_mono s Hi t E e rec Φ Ψ Φr Ψr :
  wpr s Hi t E e rec Φ Φr -∗
  (∀ v, Φ v ==∗ Ψ v) ∧ (∀ Hi t v, Φr Hi t v ==∗ Ψr Hi t v) -∗
  wpr s Hi t E e rec Ψ Ψr.
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
Lemma idempotence_wpr s E e rec Φx Φrx Φcx Hi t:
  ((WPC e @ s ; E ; ∅ {{ Φx t }} {{ Φcx t }}) -∗
   (□ ∀ (H: invG Σ) (t: pbundleG T Σ) σ σ' (HC: crash_prim_step CS σ σ') κs n,
        Φcx t -∗ state_interp σ κs n ={∅}=∗
        ▷ ∀ H', ∃ t', state_interp σ' κs 0 ∗ WPC rec @ s ; E ; ∅ {{ Φrx H' t' }} {{ Φcx t' }}) -∗
    wpr s Hi t E e rec (Φx t) Φrx)%I.
Proof.
  iLöb as "IH" forall (E e Hi t Φx).
  iIntros "He #Hidemp".
  rewrite wpr_unfold. rewrite /wpr_pre.
  iApply (wpc_strong_mono with "He"); [ auto | auto | auto | ].
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
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : invG Σ → pbundleG T Σ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Notation wptp s t := ([∗ list] ef ∈ t, WPC ef @ s; ⊤; ∅ {{ fork_post }} {{ True }})%I.

Lemma wptp_recv_strong_adequacy Φ Φr κs' s Hi t n ns r1 e1 t1 κs t2 σ1 σ2 :
  nrsteps (CS := CS) r1 (n :: ns) (e1 :: t1, σ1) κs (t2, σ2) Normal →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  wpr s Hi t ⊤ e1 r1 Φ Φr -∗
  wptp s t1 ={⊤,∅}▷=∗^(S n) (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v)).
Proof.
  iIntros (Hstep) "Hσ He Ht".
  inversion Hstep. subst.
  iPoseProof (wptp_strong_adequacy with "Hσ [He] Ht") as "H".
  { eauto. }
  {rewrite wpr_unfold /wpr_pre. iApply "He". }
  rewrite perennial_invG.
  iApply "H".
Qed.

Fixpoint fupd_fresh (ns: list nat) Hi0 (P: invG Σ → iProp Σ) :=
  match ns with
  | [] => P Hi0
  | (n :: ns) =>
    (|={⊤}=> ∀ Hi', fupd_fresh ns Hi' P)%I
  end.

Fixpoint step_fupdN_fresh (ns: list nat) Hi0 t0 (P: invG Σ → pbundleG T Σ → iProp Σ) :=
  match ns with
  | [] => P Hi0 t0
  | (n :: ns) =>
    (|={⊤, ∅}▷=>^(S n) |={⊤, ∅}=> ▷
     ∀ Hi', (∃ t' : pbundleG T Σ, step_fupdN_fresh ns Hi' t' P))%I
  end.


Lemma step_fupdN_fresh_snoc (ns: list nat) n Hi0 t0 Q:
  step_fupdN_fresh (ns ++ [n]) Hi0 t0 Q ≡
  step_fupdN_fresh (ns) Hi0 t0 (λ Hi _, |={⊤, ∅}▷=>^(S n) |={⊤, ∅}=> ▷ ∀ Hi', ∃ t', Q Hi' t')%I.
Proof.
  apply (anti_symm (⊢)%I).
  - revert Hi0 t0 Q.
    induction ns => ??? //=. do 3 f_equiv.
    apply step_fupdN_mono.
    do 2 f_equiv. do 2 (f_equiv => ?).
    rewrite IHns. eauto.
  - revert Hi0 t0 Q.
    induction ns => ??? //=. do 3 f_equiv.
    apply step_fupdN_mono.
    do 2 f_equiv. do 2 (f_equiv => ?).
    rewrite IHns. eauto.
Qed.

Lemma step_fupdN_fresh_pattern_wand {H: invG Σ} n (Q Q': iProp Σ):
  (|={⊤, ∅}▷=>^(S n) |={⊤, ∅}=> ▷ Q) -∗ (Q -∗ Q') -∗
  (|={⊤, ∅}▷=>^(S n) |={⊤, ∅}=> ▷ Q').
Proof.
  iIntros "H Hwand". simpl.
  iApply (step_fupdN_wand with "H").
  iNext. iIntros "H".
  iMod "H". iModIntro. iNext.
  by iApply "Hwand".
Qed.

Lemma step_fupdN_fresh_pattern_plain {H: invG Σ} n (Q: iProp Σ) `{!Plain Q}:
  (|={⊤, ∅}▷=>^(S n) |={⊤, ∅}=> ▷ Q)-∗
  (|={⊤}=> ▷^(S (S n)) Q).
Proof.
  iIntros "H".
  iDestruct (step_fupdN_wand with "H []") as "H".
  { iApply fupd_plain_mask_empty. }
  rewrite -step_fupdN_S_fupd.
  iDestruct (step_fupdN_plain with "H") as "H".
  iMod "H". iModIntro. iNext. rewrite -later_laterN laterN_later. iNext. by iMod "H".
Qed.

Lemma step_fupdN_fresh_wand (ns: list nat) Hi0 t0 Q Q':
  step_fupdN_fresh (ns) Hi0 t0 Q -∗ (∀ Hinv t, Q Hinv t -∗ Q' Hinv t)
  -∗ step_fupdN_fresh ns Hi0 t0 Q'.
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

Lemma step_fupdN_fresh_snoc_plain ns n Hinv t0 P `{!Plain P}:
  step_fupdN_fresh (ns ++ [n]) Hinv t0 (λ (x : invG Σ) (t : pbundleG T Σ), P) -∗
  step_fupdN_fresh ns Hinv t0 (λ (x : invG Σ) (t : pbundleG T Σ), |={⊤}=> ▷^(S (S n)) P).
Proof.
  iIntros "H".
  rewrite ?step_fupdN_fresh_snoc.
  iApply (step_fupdN_fresh_wand with "H").
  { iIntros (Hinv' ?) "H".
   iDestruct (step_fupdN_wand _ _ _ _ (|={⊤}=> ▷ P)%I with "H []") as "H'".
   { iIntros "H". iApply fupd_plain_mask_empty.  iMod "H". iModIntro.
     iNext. iDestruct ("H" $! Hinv') as (_) "$". }
   rewrite -step_fupdN_S_fupd.
   iMod (step_fupdN_plain with "H'") as "Hφ". iModIntro. simpl. iNext.
   rewrite -later_laterN laterN_later.
   iNext. by iMod "Hφ".
  }
Qed.

Lemma fupd_fresh_plain_1 `{!invPreG Σ} P `{!Plain P} ns:
  (∀ Hinv', fupd_fresh ns Hinv' (λ _, P)) ==∗ ◇ P.
Proof.
  iIntros "H".
  iInduction ns as [| n ns] "IH".
  - simpl. iMod wsat_alloc as (Hinv) "(Hw&HE)". iApply ("H" $! Hinv).
  - iMod wsat_alloc as (Hinv) "(Hw&HE)".
    iSpecialize ("H" $! Hinv).
    simpl.
    rewrite uPred_fupd_eq /uPred_fupd_def.
    iMod ("H" with "[$]") as "[Hw [HE H]]".
    iMod "H". by iApply "IH".
Qed.

Fixpoint fresh_later_count (ns: list nat) :=
  match ns with
  | [] => 2
  | n :: ns' => (S (S n)) + fresh_later_count ns'
  end.

Lemma step_fupdN_fresh_plain `{!invPreG Σ} P `{!Plain P} ns:
  (∀ Hinv', ∃ t, step_fupdN_fresh ns Hinv' t (λ _ _, P)) -∗ ▷^(fresh_later_count ns) P.
Proof.
  iIntros "H".
  iInduction ns as [| n' ns] "IH".
  - simpl. iApply bupd_plain; try (iPureIntro; apply _).
    iMod wsat_alloc as (Hinv) "(Hw&HE)". by iDestruct ("H" $! Hinv) as (_) "$".
  - iMod wsat_alloc as (Hinv) "(Hw&HE)".
    iSpecialize ("H" $! Hinv).
    iDestruct "H" as (t) "H".
    rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    iDestruct (step_fupdN_fresh_pattern_wand with "H IH") as "H".
    iDestruct (step_fupdN_fresh_pattern_plain with "H") as "H".
    rewrite {1}uPred_fupd_eq {1}/uPred_fupd_def.
    iMod ("H" with "[$]") as "[Hw [HE >H]]".
    by rewrite laterN_plus.
Qed.

Lemma fupd_fresh_plain_soundness `{!invPreG Σ} (P: iProp Σ) `{!Plain P} ns:
  (∀ `{Hinv: !invG Σ}, bi_emp_valid (fupd_fresh ns Hinv (λ _, P))) → bi_emp_valid P.
Proof.
  iIntros (Hfupd).
  apply later_soundness.
  iAssert (∀ Hinv, fupd_fresh ns Hinv (λ _: invG Σ, P))%I as "H".
  { iIntros. iApply Hfupd. }
  clear Hfupd.
  iInduction ns as [| n ns] "IH".
  - simpl. iMod wsat_alloc as (Hinv) "_". iApply ("H" $! Hinv).
  - iMod wsat_alloc as (Hinv) "[Hw HE]".
    iSpecialize ("H" $! Hinv).
    simpl.
    rewrite uPred_fupd_eq /uPred_fupd_def.
    iMod ("H" with "[$]") as "[Hw [HE >H']]".
    iApply ("IH" with "H'").
Qed.

Lemma step_fupdN_fresh_soundness' `{!invPreG Σ} (φ : Prop) ns:
  (∀ Hinv : invG Σ, (∃ t0, step_fupdN_fresh ns Hinv t0 (λ _ _, ⌜φ⌝))%I) →
  φ.
Proof.
  intros Hiter.
  apply (soundness (M:=iResUR Σ) _  (fresh_later_count ns)); simpl.
  iApply step_fupdN_fresh_plain. iIntros (Hinv). iApply Hiter.
Qed.

(*
Notation "|={ E }=>_( t ) Q" := (fupd (FUpd := t) E E Q)
 (at level 99) : bi_scope.
Notation "P ={ E }=∗_ t Q" := (P -∗ |={E}=>_(t) Q)%I
 (at level 99) : bi_scope.
*)

(*
Lemma wptp_recv_strong_crash_adequacy Φ Φr κs' s Hi t ns n r1 e1 t1 κs t2 σ1 σ2 :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, σ1) κs (t2, σ2) Crashed →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  wpr s Hi t ⊤ e1 r1 Φ Φr -∗
  wptp s t1 -∗ step_fupdN_fresh ns Hi t (λ Hi' t',
    (|={⊤, ∅}▷=>^(S n) |={⊤, ∅}=> ▷ ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    from_option (Φr Hi' t') True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v))).
Proof.
  revert Hi t e1 t1 κs κs' t2 σ1 σ2 Φ.
  induction ns as [|n' ns' IH] => Hi t e1 t1 κs κs' t2 σ1 σ2 Φ.
  (*
  { inversion_clear 1. }
   *)
  iIntros (Hsteps) "Hσ He Ht".
  inversion_clear Hsteps as [|?? [t1' σ1'] ????? s0].
  rewrite {1}/step_fupdN_fresh -/step_fupdN_fresh.
  destruct ρ2 as (?&σ2_pre_crash).
  iApply (step_fupdN_wand with "[-]").
  { rewrite -assoc wpr_unfold /wpr_pre.
    iPoseProof (@wptp_strong_crash_adequacy with "[$] [$]") as "H"; eauto.
    rewrite perennial_invG. by iApply "H".
  }
  iIntros "H". iMod "H" as (e2 t2' ?) "(H&Hσ)".
  iMod ("H" with "[//] Hσ") as "H". iModIntro. iNext.
  destruct s0.
  - iIntros (Hi'). iSpecialize ("H" $! Hi').
    iDestruct "H" as (t') "(Hσ&Hr)".
    iPoseProof (IH with "[Hσ] Hr []") as "H"; eauto.
  - iIntros (Hi').
    iDestruct ("H" $! Hi') as (t') "(Hσ&Hr)".
    iExists t'. subst. inversion H1; subst.
    rewrite /step_fupdN_fresh.
    iPoseProof (wptp_strong_adequacy with "[Hσ] [Hr] []") as "H"; eauto.
    { rewrite wpr_unfold /wpr_pre. iApply "Hr". }
    rewrite perennial_invG.
    iApply (step_fupdN_wand with "H").
    iIntros "H". iDestruct "H" as (????) "(Hσ&?&?)".
    iApply (fupd_mask_weaken _ ∅); first by set_solver+.
    iNext. iIntros (Hi''). iExists t', _, _. iFrame.
    iSplitL ""; eauto. (* *)
Abort.
*)


(* XXX: Use of step_fupdN_fresh modality here does "an extra" crash *)
Lemma wptp_recv_strong_crash_adequacy Φ Φr κs' s Hi t ns r1 e1 t1 κs t2 σ1 σ2 :
  nrsteps (CS := CS) r1 ns (e1 :: t1, σ1) κs (t2, σ2) Crashed →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  wpr s Hi t ⊤ e1 r1 Φ Φr -∗
  wptp s t1 -∗ step_fupdN_fresh ns Hi t (λ Hi' t', ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2) ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    from_option (Φr Hi' t') True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v)).
Proof.
  revert Hi t e1 t1 κs κs' t2 σ1 σ2 Φ.
  induction ns as [|n ns' IH] => Hi t e1 t1 κs κs' t2 σ1 σ2 Φ.
  { inversion_clear 1. }
  iIntros (Hsteps) "Hσ He Ht".
  inversion_clear Hsteps as [|?? [t1' σ1'] ????? s0].
  rewrite {1}/step_fupdN_fresh -/step_fupdN_fresh.
  destruct ρ2 as (?&σ2_pre_crash).
  iApply (step_fupdN_wand with "[-]").
  { rewrite -assoc wpr_unfold /wpr_pre.
    iPoseProof (@wptp_strong_crash_adequacy with "[$] [$]") as "H"; eauto.
    rewrite perennial_invG. by iApply "H".
  }
  iIntros "H". iMod "H" as (e2 t2' ?) "(H&Hσ)".
  iMod ("H" with "[//] Hσ") as "H". iModIntro. iNext.
  destruct s0.
  - iIntros (Hi'). iSpecialize ("H" $! Hi').
    iDestruct "H" as (t') "(Hσ&Hr)".
    iPoseProof (IH with "[Hσ] Hr []") as "H"; eauto.
  - iIntros (Hi').
    iDestruct ("H" $! Hi') as (t') "(Hσ&Hr)".
    iExists t'. subst. inversion H1; subst.
    rewrite /step_fupdN_fresh.
    iPoseProof (wptp_strong_adequacy with "[Hσ] [Hr] []") as "H"; eauto.
    { rewrite wpr_unfold /wpr_pre. iApply "Hr". }
    rewrite perennial_invG.
    iApply (step_fupdN_wand with "H").
    iIntros "H". iDestruct "H" as (????) "(Hσ&?&?)".
    iApply (fupd_mask_weaken _ ∅); first by set_solver+.
    iNext. iIntros (Hi''). iExists t', _, _. iFrame.
    iSplitL ""; eauto. (* *)
Abort.
(*
Qed.
*)
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

(*
Corollary wp_recv_adequacy Σ Λ CS (T: ofeT) `{!invPreG Σ} s e r σ φ φr :
  (∀ `{Hinv : !invG Σ} κs,
     (|={⊤}=> ∃ (t: pbundleG T)
         (invT: pbundleG T → invG Σ)
         (stateI : pbundleG T → state Λ → list (observation Λ) → iProp Σ)
         (fork_post : pbundleG T → val Λ → iProp Σ),
        let _ : perennialG Λ CS _ Σ :=
            PerennialG _ _ T Σ
              (λ t,
               IrisG Λ Σ (invT t) (λ σ κs _, stateI t σ κs)
                    (fork_post t))
               in
       stateI t σ κs ∗ wpr s t ⊤ e r (λ v, ⌜φ v⌝) (λ _ v, ⌜φr v⌝))%I) →
  recv_adequate (CS := CS) s e r σ (λ v _, φ v) (λ v _, φr v) .
Proof.
  intros Hwp. split.
  - intros t2 σ2 v2 [n [κs ?]]%erased_rsteps_nrsteps.
    eapply (step_fupdN_soundness' _ (S (S n)))=> Hinv. rewrite Nat_iter_S.
  eapply (wp_recv_strong_adequacy Σ _); [|done]=> ?.
  econstructor. apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod Hwp as (stateI fork_post) "[Hσ Hwp]".
  iExists s, (λ σ κs _, stateI σ κs), (λ v, ⌜φ v⌝%I), fork_post.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> ?) "_ H _".
  iApply fupd_mask_weaken; [done|]. iSplit; [|done].
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.

*)
