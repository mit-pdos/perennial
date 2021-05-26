From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Import crash_weakestpre.
From Perennial.program_logic Require Export na_crash_inv.

From Perennial.goose_lang Require Export lang typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode notation crash_borrow.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Import lock.

Opaque crash_borrow.

Set Default Proof Using "Type".
Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.

Section proof.
  Context `{!heapGS Σ, stagedG Σ} (Nlock: namespace).

  Definition is_free_crash_lock lk : iProp Σ :=
    is_free_lock lk ∗ pre_borrow.

  Definition is_crash_lock (lk: val) (R Rcrash: iProp Σ) : iProp Σ :=
    is_lock Nlock lk (crash_borrow R Rcrash).

  Definition crash_locked lk R Rcrash : iProp Σ :=
    (crash_borrow R Rcrash ∗
     is_lock Nlock lk (crash_borrow R Rcrash) ∗
     locked lk)%I.

  Definition partial_crash_locked lk R Rcrash : iProp Σ :=
    (∃ R' Rcrash',
     □ (R' -∗ Rcrash') ∗
     □ (Rcrash' -∗ Rcrash ∗ (Rcrash -∗ Rcrash')) ∗
     crash_borrow R Rcrash ∗
     crash_borrow ((R -∗ R') ∧ (Rcrash -∗ Rcrash')) (Rcrash -∗ Rcrash') ∗
     is_lock Nlock lk (crash_borrow R' Rcrash') ∗
     locked lk)%I.

  Lemma wp_new_free_crash_lock :
    {{{ True }}} lock.new #() {{{ lk, RET #lk; is_free_crash_lock lk }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply (wpc_wp _ O).
    iApply wpc_crash_borrow_generate_pre; auto.
    iApply wp_wpc.
    wp_apply wp_new_free_lock.
    iIntros. iApply "HΦ". iFrame.
  Qed.

  Lemma newlock_crash_spec k (P R Rcrash : iProp Σ) K `{!LanguageCtx K} Φ Φc :
    R -∗
    □ (R -∗ Rcrash) -∗
    Φc ∧ (∀ lk, is_crash_lock lk R Rcrash -∗ WPC (K (of_val lk)) @ k; ⊤ {{ Φ }} {{ Φc }}) -∗
    WPC K (lock.new #()) @ k; ⊤ {{ Φ }} {{ Φc ∗ Rcrash }}.
  Proof.
    iIntros "HR #Hwand1 Hwpc".
    iApply (wpc_crash_borrow_init_ctx' _ _ _ _ _ R Rcrash with "[$] [$] [-]").
    { auto. }
    iSplit.
    { iDestruct "Hwpc" as "($&_)". }
    iIntros "Hborrow".
    iApply (wp_wpc_frame').
    iSplitL "Hwpc".
    { iExact "Hwpc". }

    iApply (newlock_spec Nlock _ (crash_borrow R Rcrash) with "[$Hborrow]").
    iNext.
    iIntros (lk) "His_lock HP".
    iApply "HP". eauto.
  Qed.

  Lemma alloc_crash_lock k Φ Φc e lk (R Rcrash : iProp Σ):
    □ (R -∗ Rcrash) ∗
    R ∗
    is_free_crash_lock lk ∗
    (is_crash_lock #lk R Rcrash -∗
          WPC e @ k; ⊤ {{ Φ }} {{ Rcrash -∗ Φc }}) -∗
    WPC e @ k; ⊤ {{ Φ }} {{ Φc }}.
  Proof.
    clear.
    iIntros "(#HRcrash&HR&Hfree&Hwp)".
    iDestruct "Hfree" as "(Hfree1&Htoks)".
    iApply (wpc_crash_borrow_inits with "[$] HR HRcrash").
    iIntros "Hborrow".
    iMod (alloc_lock with "[$] [Hborrow]") as "H".
    { iNext. iExact "Hborrow". }
    iApply "Hwp". iFrame.
  Qed.

  Lemma acquire_spec E (R Rcrash : iProp Σ) lk:
    ↑Nlock ⊆ E →
    {{{ is_crash_lock lk R Rcrash }}}
    lock.acquire lk @ E
    {{{ RET #(); crash_locked lk R Rcrash }}}.
  Proof.
    iIntros (? Φ) "#Hcrash HΦ".
    wp_apply (acquire_spec' with "Hcrash"); auto.
    iIntros "(?&?)". iApply "HΦ". iFrame. iFrame "#".
  Qed.

  Lemma partial_try_acquire_spec E lk R Rcrash R' Rcrash':
    ↑Nlock ⊆ E →
    □ (R' -∗ R ∗ (R -∗ R') ∧ (Rcrash -∗ Rcrash')) -∗
    □ (R -∗ Rcrash) -∗
    □ (Rcrash' -∗ Rcrash ∗ (Rcrash -∗ Rcrash')) -∗
    {{{ is_crash_lock lk R' Rcrash' }}} lock.try_acquire lk @ E
    {{{ b, RET #b; if b is true then partial_crash_locked lk R Rcrash else True }}}.
  Proof.
    iIntros (?) "#Hw1 #Hw2 #Hw3".
    iIntros (Φ) "!> Hl HΦ".
    rewrite /is_crash_lock/is_lock.
    iDestruct "Hl" as (l ->) "#Hinv".
    wp_rec. wp_bind (CmpXchg _ _ _). iInv Nlock as ([]) "[Hl HR]".
    - wp_cmpxchg_fail. iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
      wp_pures. iApply ("HΦ" $! false). done.
    - iDestruct "HR" as "[Hl2 HR]".
      iCombine "Hl Hl2" as "Hl".
      rewrite Qp_quarter_three_quarter.
      iApply (wpc_wp NotStuck 0 _ _ _ True).
      iAssert (▷ □ (R' -∗ Rcrash'))%I with "[HR]" as "#Hwand".
      { iNext. by iApply crash_borrow_crash_wand. }
      iApply (wpc_crash_borrow_split _ _ _ _ _ _ _
                                     R
                                     ((R -∗ R') ∧ (Rcrash -∗ Rcrash'))
                                     Rcrash
                                     (Rcrash -∗ Rcrash')
                with "HR"); auto.
      { iNext. iModIntro. iIntros "H". iDestruct "H" as "(_&$)". }
      { iNext. iIntros "(HR1&HR2)". iApply "HR2"; eauto. }
      iApply wp_wpc.
      wp_cmpxchg_suc.
      iModIntro.
      iEval (rewrite -Qp_quarter_three_quarter) in "Hl".
      iDestruct (fractional.fractional_split_1 with "Hl") as "[Hl1 Hl2]".
      iIntros "(Hc1&Hc2)".
      iSplit; first done. iModIntro.
      iSplitL "Hl1".
      { iNext; iExists true; eauto. }
      wp_pures. iApply "HΦ". iModIntro.
      rewrite /partial_crash_locked.
      iExists _, _. iFrame "∗ #".
      rewrite /is_lock/locked.
      iSplitL ""; eauto.
  Qed.

  Lemma partial_acquire_spec E lk R Rcrash R' Rcrash':
    ↑Nlock ⊆ E →
    □ (R' -∗ R ∗ (R -∗ R') ∧ (Rcrash -∗ Rcrash')) -∗
    □ (R -∗ Rcrash) -∗
    □ (Rcrash' -∗ Rcrash ∗ (Rcrash -∗ Rcrash')) -∗
    {{{ is_crash_lock lk R' Rcrash' }}} lock.acquire lk @ E {{{ RET #(); partial_crash_locked lk R Rcrash }}}.
  Proof.
    iIntros (?) "#H1 #H2 #H3". iIntros (Φ) "!> #Hl HΦ". iLöb as "IH". wp_rec.
    iPoseProof (partial_try_acquire_spec E with "H1 H2") as "H"; first done.
    wp_apply "H"; auto.
    iIntros ([]).
    - iIntros "Hlked". wp_if. iApply "HΦ"; by iFrame.
    - iIntros "_". wp_if. iApply ("IH" with "[HΦ]"). auto.
  Qed.

  Lemma use_crash_locked E1 k e lk R Rcrash Φ Φc :
    to_val e = None →
    crash_locked lk R Rcrash -∗
    Φc ∧ (R -∗ WPC e @ k; E1 {{ λ v, (crash_locked lk R Rcrash -∗ (Φc ∧ Φ v)) ∗ R }}
                                         {{ Φc ∗ Rcrash }}) -∗
    WPC e @ k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (?) "Hcrash_locked H".
    iDestruct "Hcrash_locked" as "(Hfull&#His_lock&Hlocked)".
    iApply (wpc_crash_borrow_open with "[$]"); auto.
    iSplit.
    - iDestruct "H" as "($&_)".
    - iIntros "HR". iDestruct "H" as "(_&H)".
      iSpecialize ("H" with "[$]").
      iApply (wpc_strong_mono with "H"); eauto.
      iSplit.
      * iIntros (?) "(Hclose&?)". iModIntro. iFrame. iFrame "#".
        iIntros. iApply "Hclose". iFrame; eauto.
      * iIntros.  iIntros "!>". eauto.
  Qed.

  Lemma release_spec E (R Rcrash : iProp Σ) lk:
    ↑Nlock ⊆ E →
    {{{ crash_locked lk R Rcrash }}}
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

  Lemma partial_release_spec E (R Rcrash : iProp Σ) lk:
    ↑Nlock ⊆ E →
    {{{ partial_crash_locked lk R Rcrash }}}
    lock.release lk @ E
    {{{ RET #(); True }}}.
  Proof.
    iIntros (? Φ) "Hcrash_locked HΦ".
    iDestruct "Hcrash_locked" as (??) "(#Hw1&#Hw2&Hc1&Hc2&His_lock&Hlocked)".
    rewrite /is_lock.
    iDestruct "His_lock" as (l ->) "#Hinv".
    rewrite /lock.release /=. wp_lam.
    wp_bind (CmpXchg _ _ _).
    iInv Nlock as (b) "[>Hl _]".

    iDestruct (locked_loc with "Hlocked") as "Hl2".
    iDestruct (heap_mapsto_agree with "[$Hl $Hl2]") as %->.
    iCombine "Hl Hl2" as "Hl".
    rewrite Qp_quarter_three_quarter.
    iApply (wpc_wp NotStuck 0 _ _ _ True).
    iApply (wpc_crash_borrow_combine _ _ _ _ _ R' Rcrash'
                  with "Hc1 Hc2"); auto.
    { iNext. iIntros "(HR&Hw)". iDestruct "Hw" as "(H&_)". iApply "H". eauto. }
    iApply wp_wpc.
    wp_cmpxchg_suc.
    iModIntro.
    iIntros "Hb". iSplit; first done.
    iModIntro.
    iSplitR "HΦ"; last by wp_seq; iApply "HΦ".
    iEval (rewrite -Qp_quarter_three_quarter) in "Hl".
    iDestruct (fractional.fractional_split_1 with "Hl") as "[Hl1 Hl2]".
    iNext. iExists false. iFrame.
  Qed.

  Definition with_lock lk e :=
    (lock.acquire lk;;
     let: "v" := e in
     lock.release lk)%E.

  Lemma with_lock_spec k Φ Φc (R Rcrash : iProp Σ) lk e:
    to_val e = None →
    is_crash_lock lk R Rcrash ∗
    (Φc ∧ (R -∗ WPC e @ k; ⊤ {{ λ v, (Φc ∧ Φ #()) ∗ R }} {{ Φc ∗ Rcrash }})) -∗
    WPC (with_lock lk e) @ k ; ⊤ {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (Hnv) "(#Hcrash&Hwp)".
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
    { iIntros. iModIntro. iFrame. }
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
  | [ |- envs_entails _ (wpc _ ?k _ _ _ _) ] =>
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
