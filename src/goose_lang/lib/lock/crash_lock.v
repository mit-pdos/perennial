From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import crash_weakestpre staged_invariant.
From Perennial.program_logic Require Export na_crash_inv.

From Perennial.goose_lang Require Export lang typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode notation.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Import lock.


Set Default Proof Using "Type".
Section goose_lang.
Context `{ffi_sem: ext_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.

Section proof.
  Context `{!heapG Σ, !crashG Σ, stagedG Σ} (Nlock: namespace).

  Definition is_crash_lock k (lk: val) (R Rcrash: iProp Σ) : iProp Σ :=
    is_lock Nlock lk (na_crash_inv k R Rcrash).

  Definition crash_locked k lk R Rcrash : iProp Σ :=
    (na_crash_inv k R Rcrash ∗
     is_lock Nlock lk (na_crash_inv k R Rcrash) ∗
     locked lk)%I.

  (*
  Lemma newlock_spec K `{!LanguageCtx K} k k' E Φ Φc (R Rcrash : iProp Σ):
    (k' < k)%nat →
    □ (R -∗ Rcrash) ∗
    R ∗
    Φc ∗
    (∀ lk γ, Φc -∗ is_crash_lock (LVL k') lk R Rcrash -∗
             WPC K (of_val lk) @ (LVL k); ⊤; E {{ Φ }} {{ Φc }}) -∗
    WPC K (lock.new #()) @  (LVL (S k)); ⊤; E {{ Φ }} {{ Φc ∗ Rcrash }}.
  Proof using ext_tys.
    iIntros (?) "(#HRcrash&HR&HΦc&Hwp)".
    iMod (na_crash_inv_alloc Ncrash (LVL k') ⊤ ⊤ Rcrash R with "[HR]") as
        (γ1) "(Hfull&Hpending)".
    { iFrame "HR". iModIntro. by iApply "HRcrash". }
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
    na_crash_inv k R Rcrash
    ={E}=∗ is_crash_lock k #lk R Rcrash.
  Proof.
    clear.
    iIntros "Hfree Hfull".
    iMod (alloc_lock Nlock _ with "Hfree Hfull") as "Hlk".
    iModIntro. rewrite /is_crash_lock. eauto.
  Qed.

  Lemma alloc_crash_lock_cfupd {lk} k' (R Rcrash : iProp Σ):
    is_free_lock lk -∗
    □ (R -∗ Rcrash) -∗
    ▷ R ={⊤}=∗
    is_crash_lock (S k') #lk R Rcrash ∗
    <disc> |C={⊤, ∅}_(S k')=> Rcrash.
  Proof.
    clear.
    iIntros "Hfree #HRcrash HR".
    iPoseProof (na_crash_inv_alloc k' ⊤ Rcrash R with "[HR] HRcrash") as "H".
    { iFrame "HR". }
    iMod (fupd_level_fupd with "H") as "(Hfull&?)".
    iMod (alloc_crash_lock' with "Hfree Hfull") as "Hlk".
    by iFrame.
  Qed.

  Lemma alloc_crash_lock k k' E Φ Φc e lk (R Rcrash : iProp Σ):
    (k' < k)%nat →
    □ (R -∗ Rcrash) ∗
    ▷ R ∗
    is_free_lock lk ∗
    (is_crash_lock (S k') #lk R Rcrash -∗
          WPC e @ (S k); ⊤; E {{ Φ }} {{ Rcrash -∗ Φc }}) -∗
    WPC e @ (S k); ⊤; E {{ Φ }} {{ Φc }}.
  Proof.
    clear.
    iIntros (?) "(#HRcrash&HR&Hfree&Hwp)".
    iMod (alloc_crash_lock_cfupd k' with "Hfree HRcrash HR") as "(Hlk&Hcfupd)".
    iSpecialize ("Hwp" with "Hlk").
    iApply (wpc_crash_frame_wand with "Hwp [Hcfupd]").
    iModIntro.
    iMod "Hcfupd". do 2 iModIntro; auto.
  Qed.

  Lemma acquire_spec k E (R Rcrash : iProp Σ) lk:
    ↑Nlock ⊆ E →
    {{{ is_crash_lock k lk R Rcrash }}}
    lock.acquire lk @ E
    {{{ RET #(); crash_locked k lk R Rcrash }}}.
  Proof.
    iIntros (? Φ) "#Hcrash HΦ".
    wp_apply (acquire_spec' with "Hcrash"); auto.
    iIntros "(?&?)". iApply "HΦ". iFrame. iFrame "#".
  Qed.

  Lemma use_crash_locked E1 E2 k k' e lk R Rcrash Φ Φc:
    (S k ≤ k')%nat →
    crash_locked (S k') lk R Rcrash -∗
    <disc> ▷ Φc ∧ (▷ R -∗
         WPC e @ (S k); E1; ∅ {{ λ v, (crash_locked (S k') lk R Rcrash -∗ (<disc> ▷ Φc ∧ Φ v)) ∗ ▷ R }}
                                         {{ Φc ∗ Rcrash }}) -∗
    WPC e @ (S k); E1; E2 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (?) "Hcrash_locked H".
    iDestruct "Hcrash_locked" as "(Hfull&#His_lock&Hlocked)".
    iApply (wpc_na_crash_inv_open _ k k' (S k) with "[$] [H Hlocked]"); try iFrame; auto.
    iSplit.
    - iDestruct "H" as "($&_)".
    - iIntros "HR". iDestruct "H" as "(_&H)".
      iSpecialize ("H" with "[$]").
      iApply (wpc_strong_mono with "H"); eauto.
      iSplit.
      * iIntros (?) "(Hclose&?)". iModIntro. iFrame. iFrame "#".
        iIntros. iApply "Hclose". iFrame; eauto.
      * iIntros. rewrite difference_diag_L. by iIntros "!> $".
  Qed.

  Lemma release_spec k E (R Rcrash : iProp Σ) lk:
    ↑Nlock ⊆ E →
    {{{ crash_locked k lk R Rcrash }}}
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

  Lemma with_lock_spec k k' E Φ Φc (R Rcrash : iProp Σ) lk e:
    (S k ≤ k')%nat →
    is_crash_lock (S k') lk R Rcrash ∗
    (<disc> ▷ Φc ∧
      (▷ R -∗ WPC e @ (S k); ⊤; ∅ {{ λ v, (<disc> ▷ Φc ∧ Φ #()) ∗ ▷ R }} {{ Φc ∗ Rcrash }})) -∗
    WPC (with_lock lk e) @ (S k) ; ⊤; E {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (?) "(#Hcrash&Hwp)".
    rewrite /with_lock.
    wpc_bind (lock.acquire lk).
    wpc_frame "Hwp".
    { iDestruct "Hwp" as "($&_)".  }
    iApply (acquire_spec with "Hcrash").
    { set_solver. }
    iNext. iIntros "H Hwp".
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
    { iIntros. rewrite difference_diag_L. iModIntro. iIntros "H". repeat iModIntro; auto. }
    iIntros (?) "(H&?)". iModIntro. iFrame.
    iIntros "Hlocked".
    iSplit.
    { iDestruct "H" as "(H&_)". eauto. }

    wpc_pures.
    { iDestruct "H" as "(H&_)". eauto. }

    wpc_frame "H".
    { iDestruct "H" as "($&_)". }
    iApply (release_spec with "Hlocked").
    { auto. }
    iNext. iIntros "_ H".
    { iDestruct "H" as "(_&$)". }
  Qed.

End proof.

End goose_lang.

(* XXX: this probably doesn't work correctly anymore *)
Ltac crash_lock_open H :=
  lazymatch goal with
  | [ |- envs_entails _ (wpc _ ?k _ _ _ _ _) ] =>
    match iTypeOf H with
    | Some (_, crash_locked _ _ _ _ _) =>
      iApply (use_crash_locked with H);
      [ try lia (* LVL inequality *)
      | iSplit; [ try iFromCache | ]
      ]
    | Some (_, crash_locked _ _ _ _ _ _) =>
      fail 1 "crash_lock_open:" H "does not have correct LVL"
    | Some (_, _) => fail 1 "crash_lock_open:" H "is not a crash_locked fact"
    | None => fail 1 "crash_lock_open:" H "not found"
    end
  | _ => fail 1 "crash_lock_open: not a wpc"
  end.
