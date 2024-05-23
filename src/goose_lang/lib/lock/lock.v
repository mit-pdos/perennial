From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.program_logic Require Import weakestpre.

From Perennial.goose_lang Require Import lang typing.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.goose_lang Require Import persistent_readonly.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Export lock.impl.
Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.

Local Coercion Var' (s:string): expr := Var s.

Section proof.
  Context `{!heapGS Σ} (N : namespace).

  Definition lock_inv (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦{#1/4} #b ∗ if b then True else l ↦{#3/4} #b ∗ R)%I.

  Definition is_lock (lk : val) (R : iProp Σ) : iProp Σ :=
    (∃ l: loc, ⌜lk = #l⌝ ∧ inv N (lock_inv l R))%I.

  Theorem is_lock_flat lk R :
    is_lock lk R -∗ ⌜∃ (l:loc), lk = #l⌝.
  Proof.
    iIntros "Hl"; iDestruct "Hl" as (l) "[-> _]"; eauto.
  Qed.

  Theorem is_lock_ty lk R :
    is_lock lk R -∗ ⌜val_ty lk ptrT⌝.
  Proof.
    iIntros "Hlk".
    iDestruct (is_lock_flat with "Hlk") as (l) "->".
    iPureIntro.
    val_ty.
  Qed.

  Definition locked (lk: val) : iProp Σ := ∃ (l:loc), ⌜lk = #l⌝ ∗ l ↦{#3/4} #true.

  Lemma locked_loc (l:loc) :
    locked #l ⊣⊢ l ↦{#3/4} #true.
  Proof.
    rewrite /locked.
    iSplit; auto.
    iIntros "Hl".
    iDestruct "Hl" as (l' Heq) "Hl".
    inversion Heq; subst.
    auto.
  Qed.

  Lemma locked_exclusive (lk : val) : locked lk -∗ locked lk -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (l1 ->) "H1".
    iDestruct "H2" as (l2 ?) "H2".
    inversion H; subst.
    iCombine "H1 H2" as "H".
    iDestruct (heap_pointsto_frac_valid with "H") as %Hval.
    eauto.
  Qed.

  Global Instance lock_inv_ne l : NonExpansive (lock_inv l).
  Proof. solve_proper. Qed.
  Global Instance is_lock_ne l : NonExpansive (is_lock l).
  Proof. solve_proper. Qed.

  (** The main proofs. *)
  Global Instance is_lock_persistent l R : Persistent (is_lock l R).
  Proof. apply _. Qed.
  Global Instance locked_timeless l : Timeless (locked l).
  Proof. apply _. Qed.

  Definition is_free_lock (l: loc): iProp Σ := l ↦ #false.

  Theorem is_free_lock_ty lk :
    is_free_lock lk -∗ ⌜val_ty #lk ptrT⌝.
  Proof.
    iIntros "Hlk".
    iPureIntro.
    val_ty.
  Qed.

  Theorem alloc_lock E l R : is_free_lock l -∗ ▷ R ={E}=∗ is_lock #l R.
  Proof.
    iIntros "Hl HR".
    iMod (inv_alloc N _ (lock_inv l R) with "[Hl HR]") as "#?".
    { iIntros "!>". iExists false. iFrame.
      rewrite /is_free_lock.
      iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
      iDestruct "Hl" as "[Hl1 Hl2]".
      iFrame.
    }
    iModIntro.
    iExists l.
    iSplit; eauto.
  Qed.

  Lemma wp_new_free_lock E:
    {{{ True }}} lock.new #() @ E {{{ lk, RET #lk; is_free_lock lk }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_call.
    wp_apply wp_alloc_untyped; auto.
  Qed.

  Lemma newlock_spec E (R : iProp Σ):
    {{{ ▷ R }}} lock.new #() @ E {{{ (lk:loc), RET #lk; is_lock #lk R }}}.
  Proof.
    iIntros (Φ) "HR HΦ". rewrite -wp_fupd /lock.new /=.
    wp_lam. wp_apply wp_alloc_untyped; first by auto.
    iIntros (l) "Hl".
    iMod (alloc_lock with "[$] HR") as "Hlock".
    iModIntro.
    iApply "HΦ". iFrame.
  Qed.

  Lemma try_acquire_spec stk E lk R :
    ↑N ⊆ E →
    {{{ is_lock lk R }}} lock.try_acquire lk @ stk; E
    {{{ b, RET #b; if b is true then locked lk ∗ R else True }}}.
  Proof.
    iIntros (? Φ) "#Hl HΦ". iDestruct "Hl" as (l ->) "#Hinv".
    wp_rec. wp_bind (CmpXchg _ _ _). iInv N as ([]) "[Hl HR]".
    - wp_cmpxchg_fail. iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
      wp_pures. iApply ("HΦ" $! false). done.
    - iDestruct "HR" as "[Hl2 HR]".
      iCombine "Hl Hl2" as "Hl".
      rewrite Qp.quarter_three_quarter.
      wp_cmpxchg_suc.
      iModIntro.
      iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
      iDestruct "Hl" as "[Hl1 Hl2]".
      iSplitL "Hl1"; first (iNext; iExists true; eauto).
      rewrite /locked. wp_pures.
      iApply "HΦ".
      eauto with iFrame.
  Qed.

  Lemma acquire_spec' stk E lk R :
    ↑N ⊆ E →
    {{{ is_lock lk R }}} lock.acquire lk @ stk; E {{{ RET #(); locked lk ∗ R }}}.
  Proof.
    iIntros (? Φ) "#Hl HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_acquire_spec with "Hl"); auto. iIntros ([]).
    - iIntros "[Hlked HR]". wp_if. iApply "HΦ"; by iFrame.
    - iIntros "_". wp_if. iApply ("IH" with "[HΦ]"). auto.
  Qed.

  Lemma acquire_spec lk R :
    {{{ is_lock lk R }}} lock.acquire lk {{{ RET #(); locked lk ∗ R }}}.
  Proof. eapply acquire_spec'; auto. Qed.

  Lemma release_spec' stk E lk R :
    ↑N ⊆ E →
    {{{ is_lock lk R ∗ locked lk ∗ ▷ R }}} lock.release lk @ stk; E {{{ RET #(); True }}}.
  Proof.
    iIntros (? Φ) "(Hlock & Hlocked & HR) HΦ".
    iDestruct "Hlock" as (l ->) "#Hinv".
    rewrite /lock.release /=. wp_lam.
    wp_bind (CmpXchg _ _ _).
    iInv N as (b) "[>Hl _]".

    iDestruct (locked_loc with "Hlocked") as "Hl2".
    iDestruct (heap_pointsto_agree with "[$Hl $Hl2]") as %->.
    iCombine "Hl Hl2" as "Hl".
    rewrite Qp.quarter_three_quarter.
    wp_cmpxchg_suc.
    iModIntro.
    iSplitR "HΦ"; last by wp_seq; iApply "HΦ".
    iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
    iDestruct "Hl" as "[Hl1 Hl2]".
    iNext. iExists false. iFrame.
  Qed.

  Lemma release_spec lk R :
    {{{ is_lock lk R ∗ locked lk ∗ ▷ R }}} lock.release lk {{{ RET #(); True }}}.
  Proof. eapply release_spec'; auto. Qed.

  Lemma release_spec'' lk R :
    is_lock lk R -∗ {{{ locked lk ∗ ▷ R }}} lock.release lk {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hlock !# %Φ [??] HΦ". iApply (release_spec with "[-HΦ]"); by iFrame.
  Qed.

  (** cond var proofs *)

  Definition is_cond (c: loc) (lk : val) : iProp Σ :=
    readonly (c ↦ lk).

  Global Instance is_cond_persistent c lk :
    Persistent (is_cond c lk) := _.

  Theorem wp_newCond' lk :
    {{{ is_free_lock lk }}}
      lock.newCond #lk
    {{{ (c: loc), RET #c; is_free_lock lk ∗ is_cond c #lk }}}.
  Proof.
    rewrite /is_cond.
    iIntros (Φ) "Hl HΦ".
    wp_call.
    wp_apply wp_alloc_untyped; [ auto | ].
    iIntros (c) "Hc".
    (* FIXME: need a let binding in the implementation to do an iMod after the
    Alloc (so the goal needs to still be a WP) *)
    iMod (readonly_alloc_1 with "Hc") as "Hcond".
    wp_pures.
    iApply "HΦ". by iFrame.
  Qed.

  Theorem wp_newCond lk R :
    {{{ is_lock lk R }}}
      lock.newCond lk
    {{{ (c: loc), RET #c; is_cond c lk }}}.
  Proof.
    rewrite /is_cond.
    iIntros (Φ) "Hl HΦ".
    wp_call.
    iDestruct (is_lock_flat with "Hl") as %[l ->].
    wp_apply wp_alloc_untyped; [ auto | ].
    iIntros (c) "Hc".
    (* FIXME: need a let binding in the implementation to do an iMod after the
    Alloc (so the goal needs to still be a WP) *)
    iMod (readonly_alloc_1 with "Hc") as "Hcond".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_condSignal c lk :
    {{{ is_cond c lk }}}
      lock.condSignal #c
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_call.
    iApply ("HΦ" with "[//]").
  Qed.

  Theorem wp_condBroadcast c lk :
    {{{ is_cond c lk }}}
      lock.condBroadcast #c
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_call.
    iApply ("HΦ" with "[//]").
  Qed.

  Theorem wp_condWait c lk R :
    {{{ is_cond c lk ∗ is_lock lk R ∗ locked lk ∗ R }}}
      lock.condWait #c
    {{{ RET #(); locked lk ∗ R }}}.
  Proof.
    iIntros (Φ) "(#Hcond&#Hlock&Hlocked&HR) HΦ".
    wp_call.
    rewrite /is_cond.
    iMod (readonly_load with "Hcond") as (q) "Hc".
    wp_untyped_load.
    wp_apply (release_spec with "[$Hlock $Hlocked $HR]").
    wp_pures.
    wp_untyped_load.
    wp_apply (acquire_spec with "[$Hlock]").
    iIntros "(Hlocked&HR)".
    iApply "HΦ".
    iFrame.
  Qed.

  Theorem wp_condWaitTimeout c (t : u64) lk R :
    {{{ is_cond c lk ∗ is_lock lk R ∗ locked lk ∗ R }}}
      lock.condWaitTimeout #c #t
    {{{ RET #(); locked lk ∗ R }}}.
  Proof.
    iIntros (Φ) "Hpre HΦ".
    wp_lam. wp_pures.
    wp_apply (wp_condWait with "Hpre").
    done.
  Qed.

End proof.
End goose_lang.

Typeclasses Opaque is_lock is_cond locked.
