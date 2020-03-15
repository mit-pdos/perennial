From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import crash_weakestpre staged_invariant.
From Perennial.program_logic Require Export na_crash_inv.

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
    is_lock Nlock γlk lk (na_crash_inv_full Ncrash k R Rcrash).

  Definition crash_locked k Γ lk R Rcrash : iProp Σ :=
    (na_crash_inv_full Ncrash k R Rcrash ∗
           is_lock Nlock Γ lk (na_crash_inv_full Ncrash k R Rcrash) ∗
           locked Γ)%I.

  (*
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
    iMod (na_crash_inv_alloc Ncrash (LVL k') ⊤ ⊤ Rcrash R with "[HR]") as
        (γ1) "(Hfull&Hpending)".
    { iFrame "HR". iAlways. by iApply "HRcrash". }
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
*)


  Lemma alloc_crash_lock' k E lk (R Rcrash : iProp Σ):
    is_free_lock lk -∗
    na_crash_inv_full Ncrash k R Rcrash
    ={E}=∗ ∃ γ, is_crash_lock k γ #lk R Rcrash.
  Proof using ext_tys.
    iIntros "Hfree Hfull".
    iMod (alloc_lock Nlock _ with "Hfree Hfull") as (γ') "Hlk".
    iModIntro. iExists _. rewrite /is_crash_lock. eauto.
  Qed.

  Lemma alloc_crash_lock k k' E Φ Φc e lk (R Rcrash : iProp Σ):
    (k' < k)%nat →
    □ (R -∗ Rcrash) ∗
    R ∗
    Φc ∗
    is_free_lock lk ∗
    (∀ γ, Φc -∗ is_crash_lock (LVL k') γ #lk R Rcrash -∗
          WPC e @ (LVL k); ⊤; E {{ Φ }} {{ Φc }}) -∗
    WPC e @  (LVL (S k)); ⊤; E {{ Φ }} {{ Φc ∗ Rcrash }}.
  Proof using ext_tys.
    iIntros (?) "(#HRcrash&HR&HΦc&Hfree&Hwp)".
    iMod (na_crash_inv_alloc Ncrash (LVL k') ⊤ Rcrash R with "[HR]") as
        "(Hfull&Hpending)".
    { iFrame "HR". iAlways. by iApply "HRcrash". }
    iApply (wpc_na_crash_inv_init _ k k' Ncrash E with "[-]"); try assumption.
    iFrame.
    iMod (alloc_crash_lock' with "Hfree Hfull") as (?) "Hlk".
    iApply ("Hwp" with "[$]"). by iFrame.
  Qed.

  Lemma acquire_spec k E γ (R Rcrash : iProp Σ) lk:
    ↑Nlock ⊆ E →
    {{{ is_crash_lock k γ lk R Rcrash }}}
    lock.acquire lk @ E
    {{{ RET #(); ∃ Γ, crash_locked k Γ lk R Rcrash }}}.
  Proof.
    iIntros (? Φ) "Hcrash HΦ".
    rewrite /is_crash_lock.
    iDestruct "Hcrash" as "#His_lock".
    wp_apply (acquire_spec' with "His_lock"); auto.
    iIntros "(?&?)". iApply "HΦ". iExists _. iFrame.
    iFrame "His_lock".
  Qed.

  Lemma use_crash_locked E k k' Γ e lk R Rcrash Φ Φc:
    (S k < k')%nat →
    language.to_val e = None →
    crash_locked (LVL k') Γ lk R Rcrash -∗
    Φc ∧ (R -∗
         WPC e @ LVL k; (⊤ ∖ ↑Ncrash); ∅ {{ λ v, (crash_locked (LVL k') Γ lk R Rcrash -∗ (Φ v ∧ Φc)) ∗ R }}
                                         {{ Φc ∗ Rcrash }}) -∗
    WPC e @  (LVL (S (S k))); ⊤; E {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (??) "Hcrash_locked H".
    iDestruct "Hcrash_locked" as "(Hfull&#His_lock&Hlocked)".
    iApply (wpc_na_crash_inv_open with "[$] [H Hlocked]"); try iFrame; auto.
    iSplit.
    - iDestruct "H" as "($&_)".
    - iIntros "HR". iDestruct "H" as "(_&H)".
      iSpecialize ("H" with "[$]").
      iApply (wpc_strong_mono with "H"); eauto.
      iSplit.
      * iIntros (?) "(Hclose&?)". iModIntro. iFrame.
        iIntros. iApply "Hclose". iFrame; eauto.
      * iIntros. rewrite difference_diag_L. iApply step_fupdN_inner_later; eauto.
  Qed.

  Lemma release_spec k E Γ (R Rcrash : iProp Σ) lk:
    ↑Nlock ⊆ E →
    {{{ crash_locked k Γ lk R Rcrash }}}
    lock.release lk @ E
    {{{ RET #(); True }}}.
  Proof.
    iIntros (? Φ) "Hcrash_locked HΦ".
    iDestruct "Hcrash_locked" as "(Hfull&#His_lock&Hlocked)".
    wp_apply (release_spec' with "[His_lock Hlocked Hfull]"); swap 1 2.
    { iFrame "His_lock". iFrame. }
    { auto. }
    by iApply "HΦ".
  Qed.

  Definition with_lock lk e :=
    (lock.acquire lk;;
     let: "v" := e in
     lock.release lk)%E.

  Lemma with_lock_spec k k' E γ Φ Φc (R Rcrash : iProp Σ) lk e:
    (S k < k')%nat →
    to_val e = None →
    is_crash_lock (LVL k') γ lk R Rcrash ∗
    (Φc ∧ (R -∗ WPC e @ (LVL k); (⊤ ∖ ↑Ncrash); ∅ {{ λ v, (Φ #() ∧ Φc) ∗ R }} {{ Φc ∗ Rcrash }})) -∗
    WPC (with_lock lk e) @ (LVL (S (S k))) ; ⊤; E {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (??) "(#Hcrash&Hwp)".
    rewrite /with_lock.
    wpc_bind (lock.acquire lk).
    wpc_frame "Hwp".
    { iIntros "($&_)". }
    iApply (acquire_spec with "Hcrash").
    { set_solver. }
    iNext. iIntros "H Hwp". iDestruct "H" as (?) "H".
    wpc_pures.
    { iDestruct "Hwp" as "($&_)". }

    wpc_bind e.
    iApply (use_crash_locked with "[$]"); eauto.
    iSplit.
    { iDestruct "Hwp" as "($&_)". }
    iIntros "HR". iDestruct "Hwp" as "(_&H)".
    iSpecialize ("H" with "[$]").
    iApply (wpc_strong_mono with "H"); eauto.
    iSplit; last first.
    { iIntros. rewrite difference_diag_L. iApply step_fupdN_inner_later; eauto. }
    iIntros (?) "(H&?)". iModIntro. iFrame.
    iIntros "Hlocked".
    iSplit; last first.
    { iDestruct "H" as "(_&H)". eauto. }

    wpc_pures.
    { iDestruct "H" as "(_&H)". eauto. }

    wpc_frame "H".
    { iIntros "(_&$)". }
    iApply (release_spec with "Hlocked").
    { auto. }
    iNext. iIntros "_ H".
    { iDestruct "H" as "($&_)". }
  Qed.

End proof.

End goose_lang.
