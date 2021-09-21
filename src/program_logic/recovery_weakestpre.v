From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang crash_weakestpre.
Import uPred.

Set Default Proof Using "Type".

(*** Recovery ***)

(* The parameters of a generation that the user gets to pick each round.
Basically [generationGS] without [crashGS].
Collected in a record to make it easier to extend [generationGS].
Internal implementation detail. *)
Record generation_params {Λ Σ} := {
  gparams_state_interp : state Λ → nat → iProp Σ;
}.
Arguments generation_params : clear implicits.

Definition generation_from_params {Λ Σ} (Hc: crashGS Σ) (p : generation_params Λ Σ) :
  generationGS Λ Σ
  :=
  {| iris_crashGS := Hc;
    state_interp := gparams_state_interp p |}.

(* A recovery WP is parameterized by three predicates: [Φ] is the postcondition
   for normal non-crashing execution, [Φinv] is a condition that holds at each restart
   point, and [Φr] is the postcondition satisfied in case of a crash.
   [Φinv] can refer to the current [generationGS], which is useful for
   the higher levels to "remember" information about how that was generated.

   The program starts running in the "current generation", which is why WPR
   needs a [generationGS]; after a crash, a fresh generation can be generated. *)
Definition wpr_pre `{irisGS Λ Σ} (CS: crash_semantics Λ) (s : stuckness) (k: nat)
    (wpr : generationGS Λ Σ -d> coPset -d> expr Λ -d> expr Λ -d>
                     (val Λ -d> iPropO Σ) -d>
                     (generationGS Λ Σ -d> iPropO Σ) -d>
                     (generationGS Λ Σ -d> val Λ -d> iPropO Σ) -d> iPropO Σ) :
  generationGS Λ Σ -d> coPset -d> expr Λ -d> expr Λ -d>
  (val Λ -d> iPropO Σ) -d>
  (generationGS Λ Σ -d> iPropO Σ) -d>
  (generationGS Λ Σ -d> val Λ -d> iPropO Σ) -d>
  iPropO Σ :=
  λ (_:generationGS Λ Σ) E e rec Φ Φinv Φr,
  (WPC e @ s ; k; E
     {{ Φ }}
     {{ ∀ σ g mj D σ' (HC: crash_prim_step CS σ σ') ns κs n,
        state_interp σ n -∗ global_state_interp g ns mj D κs ={E}=∗ ▷ ∀ Hc1 q, NC q ={E}=∗
          (* Pick a new generationGS, but we provide the crashGS
             TODO(RJ): can we let them pick crashGS? *)
          ∃ (p:generation_params Λ Σ),
            let HGnew := generation_from_params Hc1 p in
            state_interp (G:=HGnew) σ' 0 ∗
            global_state_interp g (step_count_next ns) mj D κs ∗
            (Φinv HGnew ∧ wpr HGnew E rec rec (Φr HGnew) Φinv Φr) ∗ NC q}})%I.

Local Instance wpr_pre_contractive `{!irisGS Λ Σ} CS s k: Contractive (wpr_pre CS s k).
Proof.
  rewrite /wpr_pre=> n wp wp' Hwp Hgen E1 e1 rec Φ Φinv Φc.
  apply wpc_ne; eauto;
  repeat (f_contractive || f_equiv). apply Hwp.
Qed.

Definition wpr_def `{!irisGS Λ Σ} CS (s : stuckness) k :
  generationGS Λ Σ → coPset → expr Λ → expr Λ →
  (val Λ → iProp Σ) →
  (generationGS Λ Σ → iProp Σ) →
  (generationGS Λ Σ → val Λ → iProp Σ) → iProp Σ := fixpoint (wpr_pre CS s k).
Definition wpr_aux `{!irisGS Λ Σ} : seal (@wpr_def Λ Σ _). by eexists. Qed.
Definition wpr `{!irisGS Λ Σ} := wpr_aux.(unseal).
Definition wpr_eq `{!irisGS Λ Σ} : wpr = @wpr_def Λ Σ _ := wpr_aux.(seal_eq).

(* Make [generationGS] implicit.
Arguments wpr {Λ Σ _} _ _ _ {_}. *)

Section wpr.
Context `{!irisGS Λ Σ}.
Implicit Types CS : crash_semantics Λ.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : generationGS Λ Σ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma wpr_unfold CS s k HG E e rec Φ Φinv Φc :
  wpr CS s k HG E e rec Φ Φinv Φc ⊣⊢ wpr_pre CS s k (wpr CS s k) HG E e rec Φ Φinv Φc.
Proof. rewrite wpr_eq. apply (fixpoint_unfold (wpr_pre _ s k)). Qed.

(* There's a stronger version of this *)
Lemma wpr_strong_mono CS s k HG E e rec Φ Ψ Φinv Ψinv Φr Ψr :
  wpr CS s k HG E e rec Φ Φinv Φr -∗
      ((∀ v, Φ v ==∗ Ψ v) ∧ (∀ HG, Φinv HG -∗ Ψinv HG) ∧ (∀ HG v, Φr HG v ==∗ Ψr HG v)) -∗
  wpr CS s k HG E e rec Ψ Ψinv Ψr.
Proof.
  iIntros "H HΦ". iLöb as "IH" forall (e HG E Φ Ψ Φinv Ψinv Φr Ψr).
  rewrite ?wpr_unfold /wpr_pre.
  iApply (wpc_strong_mono' with "H") ; auto.
  iSplit.
  { iDestruct "HΦ" as "(H&_)". iIntros. iMod ("H" with "[$]"); eauto. }
  iDestruct "HΦ" as "(_&HΦ)".
  iIntros "H".
  iModIntro. iIntros (?????????) "Hσ Hg". iMod ("H" with "[//] Hσ Hg") as "H".
  iModIntro. iNext. iIntros (Hc' ?) "HNC".
  iMod ("H" $! Hc' with "[$]") as (p) "(?&?&H&HNC)".
  set (HG' := generation_from_params Hc' p).
  iModIntro. iExists _. iFrame.
  iSplit.
  - iDestruct "H" as "(H&_)". iDestruct "HΦ" as "(HΦ&_)". by iApply "HΦ".
  - iDestruct "H" as "(_&H)".
    iApply ("IH" with "[$]").
    iSplit; last by auto.
    { iIntros. iDestruct ("HΦ") as "(_&H)"; by iMod ("H" with "[$]"). }
Qed.

(* To prove a recovery wp for e with rec, it suffices to prove a crash wp for e,
   where the crash condition implies the precondition for a crash wp for rec *)
Lemma idempotence_wpr CS s k E1 e rec Φx Φinv Φrx (Φcx: generationGS Λ Σ → iProp Σ) HG :
  ⊢ WPC e @ s ; k ; E1 {{ Φx }} {{ Φcx HG }} -∗
   (□ ∀ (HG': generationGS Λ Σ) σ g σ' (HC: crash_prim_step CS σ σ') ns mj D κs n,
        Φcx HG' -∗ state_interp (G:=HG') σ n -∗ global_state_interp g ns mj D κs ={E1}=∗
        ▷ ∀ (Hc: crashGS Σ) q, NC q ={E1}=∗
          ∃ (HG'': generationGS Λ Σ), ⌜iris_crashGS (G:=HG'') = Hc⌝ ∗
            state_interp (G:=HG'') σ' 0 ∗ global_state_interp g (step_count_next ns) mj D κs ∗
            (Φinv HG'' ∧ WPC rec @ s ; k; E1 {{ Φrx HG'' }} {{ Φcx HG'' }}) ∗ NC q) -∗
    wpr CS s k HG E1 e rec (Φx) Φinv Φrx.
Proof.
  iLöb as "IH" forall (E1 e HG Φx).
  iIntros  "He #Hidemp".
  rewrite wpr_unfold. rewrite /wpr_pre.
  iApply (wpc_strong_mono' with "He"); [ auto | auto | auto | ].
  iSplit; first auto. iIntros "Hcx".
  iApply @fupd_mask_intro_discard.
  { set_solver +. }
  iIntros. iMod ("Hidemp" with "[ ] [$] [$] [$]") as "H".
  { eauto. }
  iModIntro. iNext. iIntros (Hc' ?) "HNC".
  iMod ("H" $! Hc' with "[$]") as (HG'' <-) "(?&?&Hc&HNC)".
  (* convert from parameterization over generationGS to generation_params. *)
  set (p := Build_generation_params _ _ state_interp).
  assert (HG'' = generation_from_params iris_crashGS p) as ->.
  { destruct HG''. done. }
  iExists p. iFrame. iModIntro.
  iSplit.
  { iDestruct "Hc" as "($&_)". }
  iDestruct "Hc" as "(_&Hc)".
  iApply ("IH" $! E1 rec _ (λ v, Φrx (generation_from_params iris_crashGS p) v)%I with "[Hc]").
  { iApply (wpc_strong_mono' with "Hc"); auto. }
  eauto.
Qed.

End wpr.

Definition wpr0_pre `{irisGS Λ Σ} (CS: crash_semantics Λ) (s : stuckness) (k: nat) (mj: fracR)
    (wpr : generationGS Λ Σ -d> coPset -d> expr Λ -d> expr Λ -d>
                     (val Λ -d> iPropO Σ) -d>
                     (generationGS Λ Σ -d> iPropO Σ) -d>
                     (generationGS Λ Σ -d> val Λ -d> iPropO Σ) -d> iPropO Σ) :
  generationGS Λ Σ -d> coPset -d> expr Λ -d> expr Λ -d>
  (val Λ -d> iPropO Σ) -d>
  (generationGS Λ Σ -d> iPropO Σ) -d>
  (generationGS Λ Σ -d> val Λ -d> iPropO Σ) -d>
  iPropO Σ :=
  λ (_:generationGS Λ Σ) E e rec Φ Φinv Φr,
  (wpc0 s k mj E e
     Φ
     (∀ σ g σ' (HC: crash_prim_step CS σ σ') ns mj D κs n,
        state_interp σ n -∗ global_state_interp g ns mj D κs ={E}=∗  ▷ ∀ Hc1 q, NC q ={E}=∗
          (* Pick a new generationGS, but we provide the crashGS
             TODO(RJ): can we let them pick crashGS? *)
          ∃ (p:generation_params Λ Σ),
            let HGnew := generation_from_params Hc1 p in
            state_interp (G:=HGnew) σ' 0 ∗
            global_state_interp g (step_count_next ns) mj D κs ∗
            (Φinv HGnew ∧ wpr HGnew E rec rec (Φr HGnew) Φinv Φr) ∗ NC q))%I.

Local Instance wpr0_pre_contractive `{!irisGS Λ Σ} CS s k mj: Contractive (wpr0_pre CS s k mj).
Proof.
  rewrite /wpr_pre=> n wp wp' Hwp HG E1 e1 rec Φ Φinv Φc.
  apply wpc0_ne; eauto;
  repeat (f_contractive || f_equiv || simpl). apply Hwp.
Qed.

Definition wpr0_def `{!irisGS Λ Σ} CS (s : stuckness) k (mj : fracR) :
  generationGS Λ Σ → coPset → expr Λ → expr Λ →
  (val Λ → iProp Σ) →
  (generationGS Λ Σ → iProp Σ) →
  (generationGS Λ Σ → val Λ → iProp Σ) → iProp Σ
  := fixpoint (wpr0_pre CS s k mj).
Definition wpr0_aux `{!irisGS Λ Σ} : seal (@wpr0_def Λ Σ _). by eexists. Qed.
Definition wpr0 `{!irisGS Λ Σ} := wpr0_aux.(unseal).
Definition wpr0_eq `{!irisGS Λ Σ} : wpr0 = @wpr0_def Λ Σ _ := wpr0_aux.(seal_eq).

Section wpr0.
Context `{!irisGS Λ Σ}.
Implicit Types CS : crash_semantics Λ.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : generationGS Λ Σ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma wpr0_unfold CS s k mj HG E e rec Φ Φinv Φc :
  wpr0 CS s k mj HG E e rec Φ Φinv Φc ⊣⊢ wpr0_pre CS s k mj (wpr0 CS s k mj) HG E e rec Φ Φinv Φc.
Proof. rewrite wpr0_eq. apply (fixpoint_unfold (wpr0_pre _ s k mj)). Qed.

Lemma wpr0_wpr CS s k mj HG E e rec Φ Φinv Φc :
  wpr CS s k HG E e rec Φ Φinv Φc -∗
  wpr0 CS s k mj HG E e rec Φ Φinv Φc.
Proof.
  iIntros "Hwpr".
  iLöb as "IH" forall (HG e Φ).
  iEval (rewrite wpr0_unfold /wpr0_pre).
  iEval (rewrite wpr_unfold /wpr_pre) in "Hwpr".
  iApply wpc0_wpc.
  iApply (wpc_strong_mono with "Hwpr"); [auto|auto|auto |].
  iSplit; first eauto.
  iIntros "H !>". iIntros (σ g σ' Hcrash ns mj' D κs n) "Hσ Hg".
  iMod ("H" with "[//] [$] [$]") as "H".
  do 2 iModIntro. iIntros (??) "HNC".
  iMod ("H" with "[$]") as (p') "(Hσ&Hg&H&HNC)".
  set (HG' := generation_from_params Hc1 p').
  iModIntro. iExists _. iFrame. iSplit.
  { iDestruct "H" as "($&_)". }
  { iApply "IH". iDestruct "H" as "(_&$)". }
Qed.

End wpr0.
