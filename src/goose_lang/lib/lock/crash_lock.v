From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import crash_weakestpre staged_invariant crash_inv.

From Perennial.goose_lang Require Export lang typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode notation.
From Perennial.goose_lang Require Import readonly.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Import lock.


Set Default Proof Using "Type".
Section goose_lang.
Context `{ffi_sem: ext_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.

Section proof.
  Context `{!heapG Σ, !lockG Σ, !crashG Σ, stagedG Σ} (Nlock Ncrash: namespace).

  Definition is_crash_lock k (γlk: gname) (lk: val) (R Rcrash: iProp Σ) : iProp Σ :=
    (∃ γ1 γ2, □ (R -∗ Rcrash) ∗ staged_inv Ncrash k (⊤ ∖ ↑Ncrash) (⊤ ∖ ↑Ncrash) γ1 γ2 Rcrash ∗
           is_lock Nlock γlk lk (staged_value Ncrash γ1 R True)).

  Lemma newlock_spec K `{!LanguageCtx K} k k' E Φ Φc (R Rcrash : iProp Σ):
    (k' < k)%nat →
    □ (R -∗ Rcrash) ∗
    R ∗
    Φc ∗
    (∀ lk γ, Φc -∗ is_crash_lock (LVL k') γ lk R Rcrash -∗
             WPC K (of_val lk) @ (LVL k); ⊤; E {{ Φ }} {{ Φc }}) -∗
    WPC K (lock.new #()) @  (LVL (S k)); ⊤; E {{ Φ }} {{ Φc ∗ Rcrash }}.
  Proof using ext_tys.
    iIntros (?) "(#HRcrash&HR&HΦc&Hwp)".
    iMod (staged_inv_alloc Ncrash (LVL k') ⊤ (⊤ ∖ ↑Ncrash) Rcrash R True%I with "[HR]") as
        (γ1 γ2) "(#Hstaged_inv&Hstaged_val&Hpending)".
    { iFrame "HR". iAlways. iIntros. iSplitL; last done. by iApply "HRcrash". }
    iApply (wpc_ci_inv _ k k' Ncrash ⊤ E with "[-]"); try assumption.
    { set_solver +. }
    iFrame. iFrame "Hstaged_inv".
    iApply wpc_bind.
    iApply wp_wpc_frame. iFrame.
    iApply (newlock_spec Nlock _ with "Hstaged_val").
    iNext. iIntros (lk γlk) "Hlk HΦc".
    iApply ("Hwp" with "[$]").
    rewrite /is_crash_lock. iExists _, _. iFrame. iFrame "#".
  Qed.

  Lemma acquire_spec K `{!LanguageCtx K} k k' E γ Φ Φc (R Rcrash : iProp Σ) lk:
    (S k < k')%nat →
    (language.to_val (K (language.of_val #())) = None) →
    is_crash_lock (LVL k') γ lk R Rcrash ∗
    Φc ∧ (▷ R -∗ WPC K (of_val #()) @ LVL k; (⊤ ∖ ↑Ncrash); ∅ {{ λ v, (Φ v ∧ Φc) ∗ R }} {{ Φc ∗ Rcrash }}) -∗
    WPC K (lock.acquire lk) @  (LVL (S (S k))); ⊤; E {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (??) "(#Hcrash&Hwp)".
    rewrite /is_crash_lock.
    iDestruct "Hcrash" as (??) "(#Hr&Hinv&His_lock)".
    iApply wpc_bind.
    wpc_frame "Hwp".
    { iIntros "($&_)". }
    iApply (acquire_spec with "His_lock").
    iNext. iIntros "(Hlocked&Hstaged) H".
    iApply (wpc_staged_invariant with "[-]"); try iFrame.
    { reflexivity. }
    4: { iFrame "Hinv".
         iSplit.
         - iDestruct "H" as "($&_)".
         - iIntros "HR". iDestruct "H" as "(_&H)".
           iSpecialize ("H" with "[$]").
           iApply (wpc_strong_mono with "H"); eauto.
           iSplit.
           * iIntros (?) "(?&?)". iModIntro. iFrame "Hr".
             iFrame. iIntros. eauto.
           * iIntros. rewrite difference_diag_L. iApply step_fupdN_inner_later; eauto.
    }
    { set_solver+. }
    { eauto. }
    { eauto. }
  Qed.

  (*
  Definition with_lock lk e :=
    (acquire lk;;
     let: "v" := e in
     release lk;;
     "v")%E.

  Lemma with_lock_spec k E γ Φ Φc (R Rcrash : iProp Σ) lk e:
    to_val e = None →
    is_crash_lock (2 * (S k)) γ lk R Rcrash ∗
    (Φc ∧ (▷ R -∗ WPC e @ k; (⊤ ∖ ↑Ncrash); ∅ {{ λ v, (Φ v ∧ Φc) ∗ R }} {{ Φc ∗ Rcrash }})) ⊢
    WPC (with_lock lk e) @  (2 * S (S k)); ⊤; E {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (?) "(#Hcrash&Hwp)".
    rewrite /is_crash_lock.
    iDestruct "Hcrash" as (??) "(#Hr&Hinv&His_lock)".
    rewrite /with_lock.
    wpc_bind (acquire lk).
    wpc_frame "Hwp".
    { iIntros "($&_)". }
    iApply (spin_lock.acquire_spec with "His_lock").
    iNext. iIntros "(Hlocked&Hstaged) Hwp".
    wpc_pures.
    { iDestruct "Hwp" as "($&_)". }

    wpc_bind e.

    iApply (wpc_staged_invariant with "[Hwp Hlocked Hstaged]"); try iFrame.
    { reflexivity. }
    { set_solver+. }
    { eauto. }
    iFrame "Hinv".
    iSplit.
    { iDestruct "Hwp" as "($&_)". }
    iIntros "HR". iDestruct "Hwp" as "(_&H)".
    iSpecialize ("H" with "[$]").
    iApply (wpc_strong_mono with "H"); eauto.
    iSplit; last first.
    { iIntros. rewrite difference_diag_L. iApply step_fupdN_inner_later; eauto. }
    iIntros (?) "(H&?)". iModIntro. iFrame "Hr".
    iFrame. iIntros "Hval".
    iSplit; last first.
    { iDestruct "H" as "(_&H)". eauto. }

    wpc_pures.
    { iDestruct "H" as "(_&H)". eauto. }

    wpc_bind (release _).
    wpc_frame "H".
    { iIntros "(_&$)". }
    iApply (release_spec with "[Hlocked Hval]").
    { iFrame "His_lock ∗". }
    iNext. iIntros "_ H".

    wpc_pures.
    { iDestruct "H" as "(_&H)". eauto. }
    { iDestruct "H" as "($&_)". }
  Qed.
  *)

End proof.

End goose_lang.
