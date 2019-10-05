From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang crash_weakestpre.

Class pbundleG (T: ofeT) := {
  pbundleT : T
}.

Class perennialG (Λ : language) (CS: crash_semantics Λ) (T: ofeT) (Σ : gFunctors) := IrisG {
  perennial_irisG :> pbundleG T → irisG Λ Σ;
}.

Definition wpr_pre `{perennialG Λ CS T Σ} (s : stuckness)
    (wpr : pbundleG T -d> coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ -d> iPropO Σ) :
  pbundleG T -d> coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ -d> iPropO Σ :=
  λ t E e rec Φ Φr,
  (WPC e @ s ; E ; ∅
     {{ Φ }}
     {{ ∀ σ σ' (HC: crash_prim_step CS σ σ') κs n,
        state_interp σ κs n ={∅}=∗  ▷ ∃ t, state_interp σ' [] 0 ∗ wpr t E rec rec (λ _, Φr) Φr }})%I.

Local Instance wpr_pre_contractive `{!perennialG Λ CS T Σ} s : Contractive (wpr_pre s).
Proof.
  rewrite /wpr_pre=> n wp wp' Hwp t E1 e1 rec Φ Φc.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wpr_def `{!perennialG Λ CS T Σ} (s : stuckness) :
  pbundleG T → coPset → expr Λ → expr Λ → (val Λ → iProp Σ) → iProp Σ → iProp Σ := fixpoint (wpr_pre s).
Definition wpr_aux `{!perennialG Λ CS T Σ} : seal (@wpr_def Λ CS T Σ _). by eexists. Qed.
Definition wpr `{!perennialG Λ CS T Σ} := wpr_aux.(unseal).
Definition wpr_eq `{!perennialG Λ CS T Σ} : wpr = @wpr_def Λ CS T Σ _ := wpr_aux.(seal_eq).

Section wpr.
Context `{!perennialG Λ CS T Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma wpr_unfold s t E e rec Φ Φc :
  wpr s t E e rec Φ Φc ⊣⊢ wpr_pre s (wpr s) t E e rec Φ Φc.
Proof. rewrite wpr_eq. apply (fixpoint_unfold (wpr_pre s)). Qed.

(* There's a stronger version of this *)
Lemma wpr_strong_mono s t E e rec Φ Ψ Φr Ψr :
  wpr s t E e rec Φ Φr -∗
  (∀ v, Φ v ==∗ Ψ v) ∧ (Φr ==∗ Ψr) -∗
  wpr s t E e rec Ψ Ψr.
Proof.
  iIntros "H HΦ". iLöb as "IH" forall (e t E Φ Ψ Φr Ψr).
  rewrite ?wpr_unfold /wpr_pre.
  iApply (wpc_strong_mono with "H") ; auto.
  iSplit.
  { iDestruct "HΦ" as "(H&_)". iIntros. iMod ("H" with "[$]"); eauto. }
  iIntros "H". 
  iModIntro. iIntros (?????) "Hinterp". iMod ("H" with "[//] Hinterp") as "H".
  iModIntro. iNext. iDestruct "H" as (?) "(?&H)".
  iExists _. iFrame. iApply ("IH" with "[$]").
  iSplit; iIntros; iDestruct ("HΦ") as "(_&H)"; by iMod ("H" with "[$]").
Qed.

(* To prove a recovery wp for e with rec, it suffices to prove a crash wp for e, where the crash
   condition implies the precondition for a crash wp for rec *)
(* XXX the second predicate for wpr should take t as an argument, so we don't have this existential *)
Lemma idempotence_wpr s E e rec Φx Φrx Φcx t:
  ((WPC e @ s ; E ; ∅ {{ Φx t }} {{ Φcx t }}) -∗
   (□ ∀ (t: pbundleG T) σ σ' (HC: crash_prim_step CS σ σ') κs n,
        Φcx t -∗ state_interp σ κs n ={∅}=∗
        ▷ ∃ t', state_interp σ' [] 0 ∗ WPC rec @ s ; E ; ∅ {{ (λ _, Φrx t') }} {{ Φcx t' }}) -∗
    wpr s t E e rec (Φx t) (∃ t', Φrx t'))%I.
Proof.
  iLöb as "IH" forall (E e t Φx).
  iIntros "He #Hidemp".
  rewrite wpr_unfold. rewrite /wpr_pre.
  iApply (wpc_strong_mono with "He"); [ auto | auto | auto | ].
  iSplit; first auto. iIntros "Hcx". iModIntro.
  iIntros. iMod ("Hidemp" with "[ ] [$] [$]") as "H".
  { eauto. }
  iModIntro. iNext. iDestruct "H" as (t') "(?&Hc)".
  iExists _. iFrame.
  iApply ("IH" $! E rec t' (λ t _, ∃ t', Φrx t')%I with "[Hc]").
  { iApply (wpc_strong_mono with "Hc"); auto. }
  eauto.
Qed.

(*
Definition recv_idemp Σ {Λ CS} `{!invPreG Σ} s (rec: expr Λ) φinv φrec :=
  (□ (∀ `{Hinv : invG Σ} σ1 σ1' κs (Hcrash: crash_prim_step CS σ1 σ1'),
        (φinv σ1 ={⊤}=∗
           ∃ (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
             (fork_post : val Λ → iProp Σ),
             let _ : irisG Λ Σ := IrisG _ _ Hinv stateI fork_post in
             stateI σ1' κs 0 ∗
             wp_crash s ⊤ rec (λ _, ∀ σ n, stateI σ [] n ={⊤, ∅}=∗ φrec σ ) φinv)))%I.

*)
