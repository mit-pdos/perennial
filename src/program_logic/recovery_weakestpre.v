From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang crash_weakestpre.
Import uPred.
(*** Recovery ***)

Class pbundleG (T: ofeT) (Σ: gFunctors) := {
  pbundleT : T;
}.

Class perennialG (Λ : language) (CS: crash_semantics Λ) (T: ofeT) (Σ : gFunctors) := PerennialG {
  perennial_irisG :> ∀ (H: invG Σ), pbundleG T Σ → irisG Λ Σ;
  perennial_invG: ∀ H t, @iris_invG _ _ (perennial_irisG H t) = H
}.

Definition wpr_pre `{perennialG Λ CS T Σ} (s : stuckness) (k: nat)
    (wpr : invG Σ -d> crashG Σ -d> pbundleG T Σ -d> coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d>
                     (invG Σ -d> pbundleG T Σ -d> iPropO Σ) -d>
                     (invG Σ -d> pbundleG T Σ -d> val Λ -d> iPropO Σ) -d> iPropO Σ) :
  invG Σ -d> crashG Σ -d> pbundleG T Σ -d> coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d>
  (invG Σ -d> pbundleG T Σ -d> iPropO Σ) -d>
  (invG Σ -d> pbundleG T Σ -d> val Λ -d> iPropO Σ) -d> iPropO Σ :=
  λ H1 H2 t E e rec Φ Φinv Φr,
  (WPC e @ s ; k; E ; E
     {{ Φ }}
     {{ ∀ σ σ' (HC: crash_prim_step CS σ σ') κs n,
        state_interp σ κs n ={∅}=∗  ▷ ∀ H1 H2 q, NC q ={⊤}=∗ ∃ t, state_interp σ' κs 0 ∗ (Φinv H1 t ∧ wpr H1 H2 t E rec rec (λ v, Φr H1 t v) Φinv Φr) ∗ NC q}})%I.

Local Instance wpr_pre_contractive `{!perennialG Λ CS T Σ} s k: Contractive (wpr_pre s k).
Proof.
  rewrite /wpr_pre=> n wp wp' Hwp ?? t E1 e1 rec Φ Φinv Φc.
  apply wpc_ne; eauto;
  repeat (f_contractive || f_equiv). apply Hwp.
Qed.

Definition wpr_def `{!perennialG Λ CS T Σ} (s : stuckness) k :
  invG Σ → crashG Σ → pbundleG T Σ → coPset → expr Λ → expr Λ → (val Λ → iProp Σ) →
  (invG Σ → pbundleG T Σ → iProp Σ) →
  (invG Σ → pbundleG T Σ → val Λ → iProp Σ) → iProp Σ := fixpoint (wpr_pre s k).
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

Lemma wpr_unfold s k Hi Hc t E e rec Φ Φinv Φc :
  wpr s k Hi Hc t E e rec Φ Φinv Φc ⊣⊢ wpr_pre s k (wpr s k) Hi Hc t E e rec Φ Φinv Φc.
Proof. rewrite wpr_eq. apply (fixpoint_unfold (wpr_pre s k)). Qed.

(* There's a stronger version of this *)
Lemma wpr_strong_mono s k Hi Hc t E e rec Φ Ψ Φinv Ψinv Φr Ψr :
  wpr s k Hi Hc t E e rec Φ Φinv Φr -∗
  (∀ v, Φ v ==∗ Ψ v) ∧ <bdisc> ((∀ Hi t, Φinv Hi t -∗ Ψinv Hi t) ∧ (∀ Hi t v, Φr Hi t v ==∗ Ψr Hi t v)) -∗
  wpr s k Hi Hc t E e rec Ψ Ψinv Ψr.
Proof.
  iIntros "H HΦ". iLöb as "IH" forall (e t Hi Hc E Φ Ψ Φinv Ψinv Φr Ψr).
  rewrite ?wpr_unfold /wpr_pre.
  iApply (wpc_strong_mono' with "H") ; auto.
  iSplit.
  { iDestruct "HΦ" as "(H&_)". iIntros. iMod ("H" with "[$]"); eauto. }
  iDestruct "HΦ" as "(_&HΦ)".
  rewrite own_discrete_idemp.
  iIntros "!> H".
  rewrite difference_diag_L.
  do 2 iModIntro. iIntros (?????) "Hinterp". iMod ("H" with "[//] Hinterp") as "H".
  iModIntro. iNext. iIntros (Hi' Hc' ?) "HNC". iMod ("H" $! Hi' Hc' with "[$]") as (?) "(?&H&HNC)".
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
Lemma idempotence_wpr s k E1 E2 e rec Φx Φinv Φrx (Φcx: invG Σ → _ → iProp Σ) Hi Hc t:
  E2 ⊆ E1 →
  ⊢ WPC e @ s ; k ; E1 ; E2 {{ Φx t }} {{ Φcx Hi t }} -∗
   (□ ∀ (H: invG Σ) (Hc: crashG Σ) (t: pbundleG T Σ) σ σ' (HC: crash_prim_step CS σ σ') κs n,
        Φcx H t -∗ state_interp σ κs n ={∅}=∗
        ▷ ∀ H' (Hc': crashG Σ) q, NC q ={⊤}=∗ ∃ t', state_interp σ' κs 0 ∗ (Φinv H' t' ∧ WPC rec @ s ; k; E1 ; E2 {{ Φrx H' t' }} {{ Φcx H' t' }}) ∗ NC q) -∗
    wpr s k Hi Hc t E1 e rec (Φx t) Φinv Φrx.
Proof.
  iLöb as "IH" forall (E1 E2 e Hi Hc t Φx).
  iIntros (?) "He #Hidemp".
  rewrite wpr_unfold. rewrite /wpr_pre.
  iApply (wpc_strong_mono' with "He"); [ auto | auto | auto | set_solver | ].
  iSplit; first auto. iIntros "!> Hcx".
  iApply @fupd_level_mask_weaken.
  { set_solver +. }
  iNext. iIntros. iMod ("Hidemp" with "[ ] [$] [$]") as "H".
  { eauto. }
  iModIntro. iNext. iIntros (Hi' Hc' ?) "HNC". iMod ("H" $! Hi' Hc' with "[$]") as (t') "(?&Hc&HNC)".
  iExists _. iFrame. iModIntro.
  iSplit.
  { iDestruct "Hc" as "($&_)". }
  iDestruct "Hc" as "(_&Hc)".
  iApply ("IH" $! E1 E2 rec Hi' Hc' t' (λ t v, Φrx Hi' t v)%I with "[//] [Hc]").
  { iApply (wpc_strong_mono' with "Hc"); rewrite ?difference_diag_L; auto. iClear "# ∗".
    iSplit; auto. iModIntro. auto.
  }
  eauto.
Qed.

End wpr.
