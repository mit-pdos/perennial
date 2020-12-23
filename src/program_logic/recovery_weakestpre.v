From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang crash_weakestpre.
Import uPred.

Set Default Proof Using "Type".

(*** Recovery ***)

Class pbundleG (T: ofeT) (Σ: gFunctors) := {
  pbundleT : T;
}.

Class perennialG (Λ : language) (CS: crash_semantics Λ) (T: ofeT) (Σ : gFunctors) := PerennialG {
  perennial_irisG :> ∀ (Hcrash: crashG Σ), pbundleG T Σ → irisG Λ Σ;
  perennial_crashG: ∀ H2 t, @iris_crashG _ _ (perennial_irisG H2 t) = H2
}.

Definition wpr_pre `{perennialG Λ CS T Σ} (s : stuckness) (k: nat)
    (wpr : crashG Σ -d> pbundleG T Σ -d> coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d>
                     (crashG Σ -d> pbundleG T Σ -d> iPropO Σ) -d>
                     (crashG Σ -d> pbundleG T Σ -d> val Λ -d> iPropO Σ) -d> iPropO Σ) :
  crashG Σ -d> pbundleG T Σ -d> coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d>
  (crashG Σ -d> pbundleG T Σ -d> iPropO Σ) -d>
  (crashG Σ -d> pbundleG T Σ -d> val Λ -d> iPropO Σ) -d> iPropO Σ :=
  λ H2 t E e rec Φ Φinv Φr,
  (WPC e @ s ; k; E
     {{ Φ }}
     {{ ∀ σ σ' (HC: crash_prim_step CS σ σ') κs n,
        state_interp σ κs n ={E}=∗  ▷ ∀ H2 q, NC q ={E}=∗ ∃ t, state_interp σ' κs 0 ∗ (Φinv H2 t ∧ wpr H2 t E rec rec (λ v, Φr H2 t v) Φinv Φr) ∗ NC q}})%I.

Local Instance wpr_pre_contractive `{!perennialG Λ CS T Σ} s k: Contractive (wpr_pre s k).
Proof.
  rewrite /wpr_pre=> n wp wp' Hwp H2crash t E1 e1 rec Φ Φinv Φc.
  apply wpc_ne; eauto;
  repeat (f_contractive || f_equiv). apply Hwp.
Qed.

Definition wpr_def `{!perennialG Λ CS T Σ} (s : stuckness) k :
  crashG Σ → pbundleG T Σ → coPset → expr Λ → expr Λ → (val Λ → iProp Σ) →
  (crashG Σ → pbundleG T Σ → iProp Σ) →
  (crashG Σ → pbundleG T Σ → val Λ → iProp Σ) → iProp Σ := fixpoint (wpr_pre s k).
Definition wpr_aux `{!perennialG Λ CS T Σ} : seal (@wpr_def Λ CS T Σ _). by eexists. Qed.
Definition wpr `{!perennialG Λ CS T Σ} := wpr_aux.(unseal).
Definition wpr_eq `{!perennialG Λ CS T Σ} : wpr = @wpr_def Λ CS T Σ _ := wpr_aux.(seal_eq).

Section wpr.
Context `{!perennialG Λ CS T Σ}.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : crashG Σ → pbundleG T Σ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma wpr_unfold s k Hc t E e rec Φ Φinv Φc :
  wpr s k Hc t E e rec Φ Φinv Φc ⊣⊢ wpr_pre s k (wpr s k) Hc t E e rec Φ Φinv Φc.
Proof. rewrite wpr_eq. apply (fixpoint_unfold (wpr_pre s k)). Qed.

(* There's a stronger version of this *)
Lemma wpr_strong_mono s k Hc t E e rec Φ Ψ Φinv Ψinv Φr Ψr :
  wpr s k Hc t E e rec Φ Φinv Φr -∗
      (∀ v, Φ v ==∗ Ψ v) ∧ <bdisc> ((∀ Hc t, Φinv Hc t -∗ Ψinv Hc t) ∧
                                    (∀ Hc t v, Φr Hc t v ==∗ Ψr Hc t v)) -∗
  wpr s k Hc t E e rec Ψ Ψinv Ψr.
Proof.
  iIntros "H HΦ". iLöb as "IH" forall (e t Hc E Φ Ψ Φinv Ψinv Φr Ψr).
  rewrite ?wpr_unfold /wpr_pre.
  iApply (wpc_strong_mono' with "H") ; auto.
  iSplit.
  { iDestruct "HΦ" as "(H&_)". iIntros. iMod ("H" with "[$]"); eauto. }
  iDestruct "HΦ" as "(_&HΦ)".
  rewrite own_discrete_idemp.
  iIntros "!> H".
  iModIntro. iIntros (?????) "Hinterp". iMod ("H" with "[//] Hinterp") as "H".
  iModIntro. iNext. iIntros (Hc' ?) "HNC". iMod ("H" $! Hc' with "[$]") as (?) "(?&H&HNC)".
  iModIntro. iExists _. iFrame.
  iSplit.
  - iDestruct "H" as "(H&_)". rewrite own_discrete_elim. iDestruct "HΦ" as "(HΦ&_)". by iApply "HΦ".
  - iDestruct "H" as "(_&H)".
    iApply ("IH" with "[$]").
    iSplit; last by auto.
    { iIntros. rewrite own_discrete_elim. iDestruct ("HΦ") as "(_&H)"; by iMod ("H" with "[$]"). }
Qed.

(* To prove a recovery wp for e with rec, it suffices to prove a crash wp for e,
   where the crash condition implies the precondition for a crash wp for rec *)
Lemma idempotence_wpr s k E1 e rec Φx Φinv Φrx (Φcx: crashG Σ → _ → iProp Σ) Hc t:
  ⊢ WPC e @ s ; k ; E1 {{ Φx t }} {{ Φcx _ t }} -∗
   (□ ∀ (Hc: crashG Σ) (t: pbundleG T Σ) σ σ' (HC: crash_prim_step CS σ σ') κs n,
        Φcx Hc t -∗ state_interp σ κs n ={E1}=∗
        ▷ ∀ (Hc': crashG Σ) q, NC q ={E1}=∗ ∃ t', state_interp σ' κs 0 ∗ (Φinv Hc' t' ∧ WPC rec @ s ; k; E1 {{ Φrx Hc' t' }} {{ Φcx Hc' t' }}) ∗ NC q) -∗
    wpr s k Hc t E1 e rec (Φx t) Φinv Φrx.
Proof.
  iLöb as "IH" forall (E1 e Hc t Φx).
  iIntros  "He #Hidemp".
  rewrite wpr_unfold. rewrite /wpr_pre.
  iApply (wpc_strong_mono' with "He"); [ auto | auto | auto | ].
  iSplit; first auto. iIntros "!> Hcx".
  iApply @fupd_level_mask_weaken.
  { set_solver +. }
  iIntros. iMod ("Hidemp" with "[ ] [$] [$]") as "H".
  { eauto. }
  iModIntro. iNext. iIntros (Hc' ?) "HNC". iMod ("H" $! Hc' with "[$]") as (t') "(?&Hc&HNC)".
  iExists _. iFrame. iModIntro.
  iSplit.
  { iDestruct "Hc" as "($&_)". }
  iDestruct "Hc" as "(_&Hc)".
  iApply ("IH" $! E1 rec Hc' t' (λ t v, Φrx Hc' t v)%I with " [Hc]").
  { iApply (wpc_strong_mono' with "Hc"); auto. }
  eauto.
Qed.

End wpr.
