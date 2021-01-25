From Perennial.Helpers Require Import ipm.

From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export staged_invariant crash_lang recovery_weakestpre.
From Perennial.program_logic Require Import crash_adequacy recovery_adequacy spec_assert.
Import uPred.

Section refinement.

Context {Λspec: language}.
Context {CSspec: crash_semantics Λspec}.
Context {Λ: language}.
Context {CS: crash_semantics Λ}.
Context `{INH: Inhabited (state Λspec)}.

Corollary wp_recv_refinement_adequacy Σ (T: ofe) (cfgT : _ → @cfgG Λspec Σ)
  `{!invPreG Σ} `{!crashPreG Σ} s k es e rs r σs σ φ φr Φinv (R: state Λspec -> state Λ -> Prop)
:
  (∀ `{Hinv : !invG Σ} `{Hc: !crashG Σ} κs,
     (|={⊤}=> ∃ (t: pbundleG T Σ)
         (stateI : pbundleG T Σ → state Λ → list (observation Λ) → iProp Σ)
         (fork_post : pbundleG T Σ → val Λ → iProp Σ) Hpf,
        let _ : perennialG Λ CS _ Σ :=
            PerennialG _ _ T Σ
              (λ Hi t,
               IrisG Λ Σ Hi (λ σ κs _, stateI t σ κs)
                    (fork_post t)) Hpf
               in
        let Φinv' := λ (Hinv: invG Σ) t,
            (@source_ctx' Λspec CSspec Σ (cfgT t) Hinv rs ([es], σs) ∗
            □ (∀ σ κ,  stateI t σ κ ={⊤ ∖ ↑ sN, ∅}=∗ ∃ σs, source_state σs ∗ ⌜ R σs σ ⌝))
            in
       Φinv' _ _ ∗
       □ (∀ Hi t, Φinv Hi t -∗ Φinv' Hi t) ∗
       stateI t σ κs ∗ wpr s k Hinv Hc t ⊤ e r (λ v, ⌜φ v⌝) Φinv (λ _ _ v, ⌜φr v⌝))%I) →
  ∀ t2 σ2 stat, erased_rsteps (CS := CS) r ([e], σ) (t2, σ2) stat →
  ∃ t2s σ2s stats,
  erased_rsteps (CS := CSspec) rs ([es], σs) (t2s, σ2s) stats ∧
  R σ2s σ2.
Proof.
  intros H t2 σ2 stat Hsteps.
  eapply recv_adequate_inv with
         (φinv := λ σ2,
                  ∃ t2s σ2s stats,
                    erased_rsteps (CS := CSspec) rs ([es], σs) (t2s, σ2s) stats ∧
                    R σ2s σ2); eauto.
  eapply wp_recv_adequacy_inv.
  { eassumption. }
  { eassumption. }
  iIntros (???).
  iMod H as (????) "((#Hsource&#HP)&#Hinv'_next&Hw&Hwpr)".
  iModIntro.
  iExists _, _, _, _. iFrame.
  iSplit.
  - iModIntro. iIntros.
    rewrite /source_ctx'.
    iInv "Hsource" as "H" "_".
    iDestruct "H" as (???) ">(Hauth&Hsteps)".
    iDestruct "Hsteps" as %(Hsteps_spec&Hsafe).
    iMod (fupd_intro_mask' _ (⊤ ∖ ↑sN)).
    { solve_ndisj. }
    iMod ("HP" with "[$]") as (σs') "(H&%)".
    iDestruct (source_state_reconcile with "[$] [$]") as %Heq.
    iModIntro. iExists _, _, _. iPureIntro. split; eauto. rewrite <-Heq. eauto.
  - (* XXX: redundancy here *)
    iModIntro. iIntros (Hi' t').
    iClear "Hsource". iClear "HP". iIntros "Hinv".
    iDestruct ("Hinv'_next" $! Hi' t' with "[$]") as "(#Hsource&#HP)".
    iModIntro. rewrite /source_ctx'.
    iIntros.
    iInv "Hsource" as "H" "_".
    iDestruct "H" as (???) ">(Hauth&Hsteps)".
    iDestruct "Hsteps" as %(Hsteps_spec&Hsafe).
    iMod (fupd_intro_mask' _ (⊤ ∖ ↑sN)).
    { solve_ndisj. }
    iMod ("HP" with "[$]") as (σs') "(H&%)".
    iDestruct (source_state_reconcile with "[$] [$]") as %Heq.
    iModIntro. iExists _, _, _. iPureIntro. split; eauto. rewrite <-Heq. eauto.
Qed.

End refinement.
