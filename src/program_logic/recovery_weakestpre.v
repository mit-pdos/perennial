From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang crash_weakestpre.
Import uPred.

Set Default Proof Using "Type".

(*** Recovery ***)

(* An irisGS instance usually depends on some implicit ghost names as part of
   state interpretation. Some of these names need to be changed as a result of a
   crash.  A pbundleG T instance is a way to declare a dependence on some type T
   which can encode this set of names *)

Class pbundleG (T: ofe) (Σ: gFunctors) := {
  pbundleT : T;
}.

(* A perennialG instance generates an irisGS instance given an element t of the designated type T and
   a crashG instance. We require some properties of the generated irisGS instances, such as that
   they all use the same num_laters_per_step function.

   TODO: for the distributed version, we also need to similarly add fields requiring that for every t,
   the invGS Σ instance is the same, and the global_state_interp function is the same *)

Class perennialG (Λ : language) (CS: crash_semantics Λ) (T: ofe) (Σ : gFunctors) := PerennialG {
  perennial_irisG :> ∀ (Hcrash: crashG Σ), pbundleG T Σ → irisGS Λ Σ;
  perennial_crashG: ∀ H2 t, @iris_crashG _ _ (perennial_irisG H2 t) = H2;
  perennial_inv_crashG: ∀ H1 H2 t, @iris_invG _ _ (perennial_irisG H1 t) =
                                   @iris_invG _ _ (perennial_irisG H2 t);
  perennial_num_laters_per_step: nat → nat;
  perennial_num_laters_per_step_spec:
    ∀ Hc Ht, (@num_laters_per_step _ _ (@perennial_irisG Hc Ht)) = perennial_num_laters_per_step;
  perennial_step_count_next: nat → nat;
  perennial_step_count_next_spec:
    ∀ Hc Ht, (@step_count_next _ _ (@perennial_irisG Hc Ht)) = perennial_step_count_next;
}.

Definition perennialG_equiv {Λ CS T Σ} (I1 I2: perennialG Λ CS T Σ) :=
  (∀ Hcrash t, irisG_equiv (@perennial_irisG _ _ _ _ I1 Hcrash t)
                           (@perennial_irisG _ _ _ _ I2 Hcrash t)).

(* A recovery WP is parameterized by three predicates: [Φ] is the postcondition
   for normal non-crashing execution, [Φr] is the postcondition satisfied in
   case of a crash, and [Φinv] is a condition that holds at each restart
   point. *)
Definition wpr_pre `{perennialG Λ CS T Σ} (s : stuckness) (k: nat)
    (wpr : crashG Σ -d> pbundleG T Σ -d> coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d>
                     (crashG Σ -d> pbundleG T Σ -d> iPropO Σ) -d>
                     (crashG Σ -d> pbundleG T Σ -d> val Λ -d> iPropO Σ) -d> iPropO Σ) :
  crashG Σ -d> pbundleG T Σ -d> coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d>
  (crashG Σ -d> pbundleG T Σ -d> iPropO Σ) -d>
  (crashG Σ -d> pbundleG T Σ -d> val Λ -d> iPropO Σ) -d> iPropO Σ :=
  λ Hc0 t0 E e rec Φ Φinv Φr,
  (WPC e @ s ; k; E
     {{ Φ }}
     {{ ∀ σ g mj D σ' (HC: crash_prim_step CS σ σ') ns κs n,
        state_interp σ n -∗ global_state_interp g ns mj D κs ={E}=∗ ▷ ∀ Hc1 q, NC q ={E}=∗
          ∃ t1
            (Hsame_inv: @iris_invG _ _ (perennial_irisG Hc1 t1) =
                        @iris_invG _ _ (perennial_irisG Hc0 t0)),
          □ (∀ g ns mj D κs, @global_state_interp _ _ (perennial_irisG Hc1 t1) g ns mj D κs ∗-∗
                             @global_state_interp _ _ (perennial_irisG Hc0 t0) g ns mj D κs) ∗
          state_interp σ' 0 ∗
          global_state_interp g (step_count_next ns) mj D κs ∗
          (Φinv Hc1 t1 ∧ wpr Hc1 t1 E rec rec (λ v, Φr Hc1 t1 v) Φinv Φr) ∗ NC q}})%I.

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
      (∀ v, Φ v ==∗ Ψ v) ∧ ((∀ Hc t, Φinv Hc t -∗ Ψinv Hc t) ∧ (∀ Hc t v, Φr Hc t v ==∗ Ψr Hc t v)) -∗
  wpr s k Hc t E e rec Ψ Ψinv Ψr.
Proof.
  iIntros "H HΦ". iLöb as "IH" forall (e t Hc E Φ Ψ Φinv Ψinv Φr Ψr).
  rewrite ?wpr_unfold /wpr_pre.
  iApply (wpc_strong_mono' with "H") ; auto.
  iSplit.
  { iDestruct "HΦ" as "(H&_)". iIntros. iMod ("H" with "[$]"); eauto. }
  iDestruct "HΦ" as "(_&HΦ)".
  iIntros "H".
  iModIntro. iIntros (?????????) "Hσ Hg". iMod ("H" with "[//] Hσ Hg") as "H".
  iModIntro. iNext. iIntros (Hc' ?) "HNC". iMod ("H" $! Hc' with "[$]") as (? Heqpf') "(Heq&?&?&H&HNC)".
  iModIntro. iExists _, Heqpf'. iFrame.
  iSplit.
  - iDestruct "H" as "(H&_)". iDestruct "HΦ" as "(HΦ&_)". by iApply "HΦ".
  - iDestruct "H" as "(_&H)".
    iApply ("IH" with "[$]").
    iSplit; last by auto.
    { iIntros. iDestruct ("HΦ") as "(_&H)"; by iMod ("H" with "[$]"). }
Qed.

(* To prove a recovery wp for e with rec, it suffices to prove a crash wp for e,
   where the crash condition implies the precondition for a crash wp for rec *)
Lemma idempotence_wpr s k E1 e rec Φx Φinv Φrx (Φcx: crashG Σ → _ → iProp Σ) Hc t:
  ⊢ WPC e @ s ; k ; E1 {{ Φx t }} {{ Φcx _ t }} -∗
   (□ ∀ (Hc: crashG Σ) (t: pbundleG T Σ) σ g σ' (HC: crash_prim_step CS σ σ') ns mj D κs n,
        Φcx Hc t -∗ state_interp σ n -∗ global_state_interp g ns mj D κs ={E1}=∗
        ▷ ∀ (Hc': crashG Σ) q, NC q ={E1}=∗
          ∃ t'
            (Hsame_global_interp: @global_state_interp _ _ (perennial_irisG Hc' t') =
                                  @global_state_interp _ _ (perennial_irisG Hc t))
            (Hsame_inv: @iris_invG _ _ (perennial_irisG Hc' t') =
                        @iris_invG _ _ (perennial_irisG Hc t)),
            state_interp σ' 0 ∗ global_state_interp g (step_count_next ns) mj D κs ∗
            (Φinv Hc' t' ∧ WPC rec @ s ; k; E1 {{ Φrx Hc' t' }} {{ Φcx Hc' t' }}) ∗ NC q) -∗
    wpr s k Hc t E1 e rec (Φx t) Φinv Φrx.
Proof.
  iLöb as "IH" forall (E1 e Hc t Φx).
  iIntros  "He #Hidemp".
  rewrite wpr_unfold. rewrite /wpr_pre.
  iApply (wpc_strong_mono' with "He"); [ auto | auto | auto | ].
  iSplit; first auto. iIntros "Hcx".
  iApply @fupd_mask_intro_discard.
  { set_solver +. }
  iIntros. iMod ("Hidemp" with "[ ] [$] [$] [$]") as "H".
  { eauto. }
  iModIntro. iNext. iIntros (Hc' ?) "HNC". iMod ("H" $! Hc' with "[$]") as (t' Heq' Heqinv') "(?&?&Hc&HNC)".
  iExists _, Heqinv'. iFrame. iModIntro.
  iSplit.
  { rewrite Heq'. iModIntro. iIntros; eauto. }
  iSplit.
  { iDestruct "Hc" as "($&_)". }
  iDestruct "Hc" as "(_&Hc)".
  iApply ("IH" $! E1 rec Hc' t' (λ t v, Φrx Hc' t v)%I with "[Hc]").
  { iApply (wpc_strong_mono' with "Hc"); auto. }
  eauto.
Qed.

End wpr.

Lemma wpr_proper_irisG_equiv {Λ CS T Σ} (I1 I2 : perennialG Λ CS T Σ) s k Hc t E Φ Φinv Φr (e r : expr Λ) :
  perennialG_equiv I1 I2 →
  @wpr _ _ _ _ I1 s k Hc t E e r Φ Φinv Φr -∗
  @wpr _ _ _ _ I2 s k Hc t E e r Φ Φinv Φr.
Proof.
  iIntros (Hequiv) "Hwp".
  iLöb as "IH" forall (e E Φ Hc t).
  iEval (rewrite wpr_unfold /wpr_pre).
  iEval (rewrite wpr_unfold /wpr_pre) in "Hwp".
  rewrite ?wpc_eq.
  iDestruct (wpc_proper_irisG_equiv with "Hwp") as "Hwp"; last first.
  { rewrite -?wpc_eq. iApply (wpc_strong_mono with "Hwp"); auto.
    iSplit.
    - iIntros. eauto.
    - iIntros "H !>".
      iIntros (σ g mj D σ' Hcrash ns κs n) "Hσ Hg".
      destruct (Hequiv Hc t) as (Heqinv&Heqcrash&Heqstate&Heqglobal&Heqfork&?&Heqnext).
      iSpecialize ("H" with "[//] [Hσ] [Hg]").
      { rewrite ?Heqstate. iApply "Hσ". }
      { rewrite ?Heqglobal. iApply "Hg". }
      rewrite ?Heqinv. iMod "H". iModIntro. iNext. iIntros (??) "HNC".
      iSpecialize ("H" with "[$]").
      destruct (Hequiv Hc1 t) as (Heqinv'&Heqcrash'&Heqstate'&Heqglobal'&Heqfork'&?&Heqnext').
      rewrite ?Heqinv'. iMod "H". iModIntro.
      iDestruct "H" as (t' Heq') "(#Heq&Hσ&Hg&H&HNC)".
      destruct (Hequiv Hc1 t') as (Heqinv''&Heqcrash''&Heqstate''&Heqglobal''&Heqfork''&?&Heqnext'').
      unshelve (iExists t', _).
      { rewrite -Heq'. rewrite Heqinv''. eauto. }
      iSplit.
      { iModIntro. iIntros. rewrite -Heqglobal -Heqglobal''. eauto. }
      rewrite ?Heqcrash'' ?Heqstate'' ?Heqglobal'' ?Heqnext''; iFrame.
      iSplit.
      { iDestruct "H" as "($&_)". }
      iApply "IH".
      iDestruct "H" as "(_&$)".
  }
  { eauto. }
Qed.

Definition wpr0_pre `{perennialG Λ CS T Σ} (s : stuckness) (k: nat) (mj: fracR)
    (wpr : crashG Σ -d> pbundleG T Σ -d> coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d>
                     (crashG Σ -d> pbundleG T Σ -d> iPropO Σ) -d>
                     (crashG Σ -d> pbundleG T Σ -d> val Λ -d> iPropO Σ) -d> iPropO Σ) :
  crashG Σ -d> pbundleG T Σ -d> coPset -d> expr Λ -d> expr Λ -d> (val Λ -d> iPropO Σ) -d>
  (crashG Σ -d> pbundleG T Σ -d> iPropO Σ) -d>
  (crashG Σ -d> pbundleG T Σ -d> val Λ -d> iPropO Σ) -d> iPropO Σ :=
  λ Hc0 t0 E e rec Φ Φinv Φr,
  (wpc0 s k mj E e
     Φ
     (∀ σ g σ' (HC: crash_prim_step CS σ σ') ns mj D κs n,
        state_interp σ n -∗ global_state_interp g ns mj D κs ={E}=∗  ▷ ∀ Hc1 q, NC q ={E}=∗
          ∃ t1
            (Hsame_inv: @iris_invG _ _ (perennial_irisG Hc1 t1) =
                        @iris_invG _ _ (perennial_irisG Hc0 t0)),
          □ (∀ g ns mj D κs, @global_state_interp _ _ (perennial_irisG Hc1 t1) g ns mj D κs ∗-∗
                             @global_state_interp _ _ (perennial_irisG Hc0 t0) g ns mj D κs) ∗
          state_interp σ' 0 ∗
          global_state_interp g (step_count_next ns) mj D κs ∗
          (Φinv Hc1 t1 ∧ wpr Hc1 t1 E rec rec (λ v, Φr Hc1 t1 v) Φinv Φr) ∗ NC q))%I.

Local Instance wpr0_pre_contractive `{!perennialG Λ CS T Σ} s k mj: Contractive (wpr0_pre s k mj).
Proof.
  rewrite /wpr_pre=> n wp wp' Hwp H2crash t E1 e1 rec Φ Φinv Φc.
  apply wpc0_ne; eauto;
  repeat (f_contractive || f_equiv). apply Hwp.
Qed.

Definition wpr0_def `{!perennialG Λ CS T Σ} (s : stuckness) k (mj : fracR) :
  crashG Σ → pbundleG T Σ → coPset → expr Λ → expr Λ → (val Λ → iProp Σ) →
  (crashG Σ → pbundleG T Σ → iProp Σ) →
  (crashG Σ → pbundleG T Σ → val Λ → iProp Σ) → iProp Σ := fixpoint (wpr0_pre s k mj).
Definition wpr0_aux `{!perennialG Λ CS T Σ} : seal (@wpr0_def Λ CS T Σ _). by eexists. Qed.
Definition wpr0 `{!perennialG Λ CS T Σ} := wpr0_aux.(unseal).
Definition wpr0_eq `{!perennialG Λ CS T Σ} : wpr0 = @wpr0_def Λ CS T Σ _ := wpr0_aux.(seal_eq).

Section wpr0.
Context `{!perennialG Λ CS T Σ}.
Implicit Types s : stuckness.
Implicit Types k : nat.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : crashG Σ → pbundleG T Σ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma wpr0_unfold s k mj Hc t E e rec Φ Φinv Φc :
  wpr0 s k mj Hc t E e rec Φ Φinv Φc ⊣⊢ wpr0_pre s k mj (wpr0 s k mj) Hc t E e rec Φ Φinv Φc.
Proof. rewrite wpr0_eq. apply (fixpoint_unfold (wpr0_pre s k mj)). Qed.

Lemma wpr0_wpr s k mj Hc t E e rec Φ Φinv Φc :
  wpr s k Hc t E e rec Φ Φinv Φc -∗
  wpr0 s k mj Hc t E e rec Φ Φinv Φc.
Proof.
  iIntros "Hwpr".
  iLöb as "IH" forall (Hc t e Φ).
  iEval (rewrite wpr0_unfold /wpr0_pre).
  iEval (rewrite wpr_unfold /wpr_pre) in "Hwpr".
  iApply wpc0_wpc.
  iApply (wpc_strong_mono with "Hwpr"); [auto|auto|auto |].
  iSplit; first eauto.
  iIntros "H !>". iIntros (σ g σ' Hcrash ns mj' D κs n) "Hσ Hg".
  iMod ("H" with "[//] [$] [$]") as "H".
  do 2 iModIntro. iIntros (??) "HNC".
  iMod ("H" with "[$]") as (He1 He2) "(Heq&Hσ&Hg&H&HNC)".
  iModIntro. iExists He1, He2. iFrame. iSplit.
  { iDestruct "H" as "($&_)". }
  { iApply "IH". iDestruct "H" as "(_&$)". }
Qed.

End wpr0.
