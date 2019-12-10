From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import staged_invariant crash_weakestpre crash_inv.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Import spin_lock.
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From Perennial.heap_lang Require Import wpc_proofmode.
Set Default Proof Using "Type".
Import uPred.

From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Export tactics lifting array.
From iris.heap_lang Require Import notation.
From Perennial.program_logic Require Import crash_weakestpre staged_invariant.
From Perennial.heap_lang Require Import wpc_proofmode.

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

  Lemma with_lock_spec k γ Φ Φc (R Rcrash : iProp Σ) lk e:
    to_val e = None →
    is_crash_lock (2 * (S k)) γ lk R Rcrash ∗
    (Φc ∧ (▷ R -∗ WPC e @ k; (⊤ ∖ ↑Ncrash); ∅ {{ λ v, (Φ v ∧ Φc) ∗ R }} {{ Φc ∗ Rcrash }})) ⊢
    WPC (with_lock lk e) @  (2 * (S (S k)))%nat; ⊤; ∅ {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (?) "(#Hcrash&Hwp)".
    rewrite /is_crash_lock.
    iDestruct "Hcrash" as (??) "(#Hr&Hinv&His_lock)".
    rewrite /with_lock.
    wpc_bind (acquire lk).
    iApply wp_wpc_frame'.
    iSplitR "Hwp"; [| iSplitR "Hwp"; [| iApply "Hwp"]].
    { iAlways; iIntros "($&_)". }
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
    iApply wp_wpc_frame'.
    iSplitR "H Hval Hlocked"; [| iSplitR "H"; [| iApply "H"]].
    { iAlways; iIntros "(_&$)". }

    iApply (release_spec with "[Hlocked His_lock Hval]").
    { iFrame "His_lock". iFrame. }
    iNext. iIntros "_ H".

    wpc_pures.
    { iDestruct "H" as "(_&H)". eauto. }
    { iDestruct "H" as "($&_)". }
  Qed.

End proof.

Section demo.
  Context `{!heapG Σ, !lockG Σ, !crashG Σ, stagedG Σ} (Nlock Ncrash: namespace).

  (* Lock protecting two memory locations, crash invariant is that the first is always either
     equal to the second, or 1 more. (Of course it doesn't make sense to do crash conditions
     about memory exclusively but it's just to illustrate). *)

  Definition counter_inv l1 l2 :=
    (∃ (z: Z), l1 ↦ #z ∗ l2 ↦ #z)%I.

  Definition counter_crash_inv l1 l2 :=
    (∃ (z: Z), l1 ↦ #z ∗ (l2 ↦ #z ∨ l2 ↦ #(z-1)))%I.

  (*
  Definition incr (lk: val) (l1 l2 : val) :=
    (acquire lk;;
     let: "v1" := !l1 in
     l1 <- "v1" + #1;;
     let: "v2" := !l2 in
     l2 <- "v2" + #1;;
     release lk)%E.
   *)

  Definition incr (lk: val) (l1 l2 : val) :=
    with_lock lk (
     let: "v1" := !l1 in
     l1 <- "v1" + #1;;
     let: "v2" := !l2 in
     l2 <- "v2" + #1)%E.

  Lemma incr_spec (lk : val) (l1 l2: loc) γ k :
    is_crash_lock Nlock Ncrash (2 * (S k)) γ lk (counter_inv l1 l2) (counter_crash_inv l1 l2) ⊢
    WPC incr lk #l1 #l2 @ (2 * (S (S k)))%nat; ⊤; ∅ {{ λ _, True }} {{ True }}.
  Proof.
    iIntros "H".
    rewrite /incr.
    iApply (with_lock_spec with "[H]"); first trivial.
    iFrame "H".
    iSplit; auto.
    iIntros "H".
    iDestruct "H" as (z) ">(?&?)".

    wpc_bind (! #l1)%E.
    iApply wpc_atomic; iSplit.
    { iModIntro; iNext. rewrite left_id. iExists _. iFrame. }
    wp_load.

    (* XXX: the ordering in the conjunction here is really annoying, should probably prefer that obligations
       relaated to crash conditions come first in all rules ?*)
    iSplit; iModIntro; last first.
    { rewrite left_id. iExists _. iFrame. }

    wpc_pures.
    { iSplitL ""; try iExists _; by iFrame. }


    wpc_bind (#l1 <- _)%E.
    iApply wpc_atomic; iSplit.
    { iModIntro; iNext. rewrite left_id. iExists _. iFrame. }

    wp_store.
    iSplit; iModIntro; last first.
    { rewrite left_id. iExists (z+1). iFrame. iRight.
      replace (z + 1 - 1) with z by lia. iFrame. }

    wpc_pures.
    { rewrite left_id. iExists (z+1). iFrame. iRight.
      replace (z + 1 - 1) with z by lia. iFrame. }


    wpc_bind (! #l2)%E.
    iApply wpc_atomic; iSplit.
    { iModIntro; iNext. rewrite left_id. iExists (z + 1).
      replace (z + 1 - 1) with z by lia. iFrame. }
    wp_load.


    iSplit; iModIntro; last first.
    { rewrite left_id. iExists (z + 1).
      replace (z + 1 - 1) with z by lia. iFrame. }

    wpc_pures.
    { rewrite left_id. iExists (z + 1).
      replace (z + 1 - 1) with z by lia. iFrame. }


    iApply wpc_atomic; iSplit.
    { iModIntro; iNext. rewrite left_id. iExists (z + 1).
      replace (z + 1 - 1) with z by lia. iFrame. }

    wp_store.
    iSplit.
    { iModIntro; iSplitL ""; eauto. iExists _; iFrame. }
    { iModIntro; iSplitL ""; eauto. iExists _; iFrame. }
  Qed.
End demo.

