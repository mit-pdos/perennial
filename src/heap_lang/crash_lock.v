From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import staged_invariant crash_weakestpre crash_inv.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Import spin_lock.
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From Perennial.heap_lang Require Import wpc_proofmode.
Set Default Proof Using "Type".
Import uPred.

Section proof.
  Context `{!heapG Σ, !lockG Σ, !crashG Σ, stagedG Σ} (Nlock Ncrash: namespace).


  Definition is_crash_lock k (γlk: gname) (lk: val) (R Rcrash: iProp Σ) : iProp Σ :=
    (∃ γ1 γ2, □ (R -∗ Rcrash) ∗ staged_inv Ncrash k (⊤ ∖ ↑Ncrash) (⊤ ∖ ↑Ncrash) γ1 γ2 Rcrash ∗
           is_lock Nlock γlk lk (staged_value Ncrash γ1 R True)).

  (* XXX: always probably want nat_scope on WPC level argument *)
  Lemma newlock_spec K `{!LanguageCtx K} k Φ Φc (R Rcrash : iProp Σ):
    □ (R -∗ Rcrash) ∗
    R ∗
    Φc ∗
    (∀ lk γ, Φc -∗ is_crash_lock k γ lk R Rcrash -∗ WPC K (of_val lk) @ S k; ⊤; ∅ {{ Φ }} {{ Φc }}) ⊢
    WPC K (newlock #()) @  (2 * (S k))%nat; ⊤; ∅ {{ Φ }} {{ Φc ∗ Rcrash }}.
  Proof.
    iIntros "(#HRcrash&HR&HΦc&Hwp)".
    iMod (staged_inv_alloc Ncrash k ⊤ (⊤ ∖ ↑Ncrash) Rcrash R True%I with "[HR]") as
        (γ1 γ2) "(#Hstaged_inv&Hstaged_val&Hpending)".
    { iFrame "HR". iAlways. iIntros. iSplitL; last done. by iApply "HRcrash". }
    iApply (wpc_ci_inv _ _ Ncrash ⊤); auto.
    iFrame. iFrame "Hstaged_inv".
    iApply wpc_bind.
    iApply wp_wpc_frame. iFrame.
    iApply (newlock_spec Nlock _ with "Hstaged_val").
    iNext. iIntros (lk γlk) "Hlk HΦc".
    iApply ("Hwp" with "[$]").
    rewrite /is_crash_lock. iExists _, _. iFrame. iFrame "#".
  Qed.

  Lemma acquire_spec K `{!LanguageCtx K} k γ Φ Φc (R Rcrash : iProp Σ) lk:
    (language.to_val (K (language.of_val #())) = None) →
    is_crash_lock (2 * (S k)) γ lk R Rcrash ∗
    Φc ∧ (▷ R -∗ WPC K (of_val #()) @ k; (⊤ ∖ ↑Ncrash); ∅ {{ λ v, (Φ v ∧ Φc) ∗ R }} {{ Φc ∗ Rcrash }}) ⊢
    WPC K (acquire lk) @  (2 * (S (S k)))%nat; ⊤; ∅ {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (?) "(#Hcrash&Hwp)".
    rewrite /is_crash_lock.
    iDestruct "Hcrash" as (??) "(#Hr&Hinv&His_lock)".
    iApply wpc_bind.
    iApply wp_wpc_frame'.
    iSplitR "Hwp"; [| iSplitR "Hwp"; [| iApply "Hwp"]].
    { iAlways; iIntros "($&_)". }
    iApply (acquire_spec with "His_lock").
    iNext. iIntros "(Hlocked&Hstaged) H".
    iApply (wpc_staged_invariant with "[-]"); try iFrame.
    { reflexivity. }
    3: { iFrame "Hinv".
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
  Qed.

  Definition with_lock lk e :=
    (acquire lk;;
     let: "v" := e in
     release lk;;
     "v")%E.

  Lemma with_lock_spec K `{!LanguageCtx K} k γ Φ Φ' Φc (R Rcrash : iProp Σ) lk e:
    to_val e = None →
    is_crash_lock (2 * (S k)) γ lk R Rcrash ∗
    (Φc ∧ (▷ R -∗ WPC e @ k; (⊤ ∖ ↑Ncrash); ∅ {{ λ v, (Φ' v ∧ Φc) ∗ R }} {{ Φc ∗ Rcrash }})) ∗
    (∀ v, Φ' v -∗ WPC (K (of_val v)) @ (2 * (S (S k)))%nat; ⊤; ∅ {{ Φ }} {{ Φc }}) ⊢
    WPC K (with_lock lk e) @  (2 * (S (S k)))%nat; ⊤; ∅ {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (?) "(#Hcrash&Hwp&HK)".
    rewrite /is_crash_lock.
    iDestruct "Hcrash" as (??) "(#Hr&Hinv&His_lock)".
    iApply wpc_bind.
    rewrite /with_lock.
    wpc_bind (acquire lk).
    iApply wp_wpc_frame'.
    iSplitR "Hwp HK"; [| iSplitR "Hwp"; [| iApply "Hwp"]].
    { iAlways; iIntros "($&_)". }
    iApply (spin_lock.acquire_spec with "His_lock").
    iNext. iIntros "(Hlocked&Hstaged) Hwp".
    wpc_pure _.
    { iDestruct "Hwp" as "($&_)". }
    wpc_pure _.
    { iDestruct "Hwp" as "($&_)". }

    wpc_bind e.

    iApply (wpc_staged_invariant with "[Hwp HK Hlocked Hstaged]"); try iFrame.
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

    wpc_pure _.
    { iDestruct "H" as "(_&H)". eauto. }

    wpc_pure _.
    { iDestruct "H" as "(_&H)". eauto. }

    wpc_bind (release _).
    iApply wp_wpc_frame'.
    iSplitR "H Hval Hlocked HK"; [| iSplitR "H"; [| iApply "H"]].
    { iAlways; iIntros "(_&$)". }

    iApply (release_spec with "[Hlocked His_lock Hval]").
    { iFrame "His_lock". iFrame. }
    iNext. iIntros "_ H".


    wpc_pure _.
    { iDestruct "H" as "(_&H)". eauto. }

    wpc_pure _.
    { iDestruct "H" as "(_&H)". eauto. }

    iApply "HK".
    { iDestruct "H" as "($&_)". }
    { iDestruct "H" as "(_&$)". }
  Qed.

End proof.
