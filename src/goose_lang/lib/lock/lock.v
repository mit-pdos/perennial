From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.program_logic Require Import weakestpre.

From Perennial.goose_lang Require Import lang typing.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Export lock.impl.
Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.

Section proof.
  Context `{!heapGS Σ} (N : namespace).

  Definition lock_inv (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, heap_pointsto l (DfracOwn (1/4)) #b ∗ if b then True else heap_pointsto l (DfracOwn (3/4)) #b ∗ R)%I.

  (**  [is_lock] takes a namespace that is used for an internal invariant.

       This is typically not relevant and can be safely set to [nroot]. It only
       matters for some crash reasoning where a lock can be acquired with some
       invariants open, but not the lock invariant itself.
   *)
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

  Definition locked (lk: val) : iProp Σ := ∃ (l:loc), ⌜lk = #l⌝ ∗ heap_pointsto l (DfracOwn (3/4)) #true.

  Lemma locked_loc (l:loc) :
    locked #l ⊣⊢ heap_pointsto l (DfracOwn (3/4)) #true.
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

  (** A "free lock" is a lock that has been allocated as unlocked and has no
  associated lock invariant. It can be later associated with a lock invariant by
  firing the [alloc_lock] fupd.

  This is especially useful when a lock is allocated for a struct field before
  the struct has been created, but needs to refer to the struct itself. There is
  a small circularity here: the mutex pointer is learned through the struct
  pointer, but the lock invariant itself refers to the struct pointer (contrast
  this with Rust, where the data protected by a Mutex must be allocated first to
  satisfy the type system).

  There is a brief time in such a proof where we rely on the fact that the lock
  has not yet been shared by other threads; it the fact that [alloc_lock] both
  takes and consumes ownership over the lock heap data that makes this sound
  (eg, the same lock cannot be associated with two different lock invariants).
  *)
  Definition is_free_lock (l: loc): iProp Σ := heap_pointsto l (DfracOwn 1) #false.

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
    {{{ True }}} newMutex #() @ E {{{ lk, RET #lk; is_free_lock lk }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec. wp_pures.
    wp_apply wp_alloc_untyped; auto.
  Qed.

  Lemma wp_newMutex E (R : iProp Σ):
    {{{ ▷ R }}} newMutex #() @ E {{{ (lk:loc), RET #lk; is_lock #lk R }}}.
  Proof.
    iIntros (Φ) "HR HΦ". rewrite -wp_fupd /newMutex /=.
    wp_rec. wp_apply wp_alloc_untyped; first by auto.
    iIntros (l) "Hl".
    iMod (alloc_lock with "[$] HR") as "Hlock".
    iModIntro.
    iApply "HΦ". iFrame.
  Qed.

  Lemma wp_Mutex__TryLock stk E lk R :
    ↑N ⊆ E →
    {{{ is_lock lk R }}} Mutex__TryLock lk @ stk; E
    {{{ b, RET #b; if b is true then locked lk ∗ R else True }}}.
  Proof.
    iIntros (? Φ) "#Hl HΦ". iDestruct "Hl" as (l ->) "#Hinv".
    wp_rec. wp_bind (CmpXchg _ _ _). iInv N as ([]) "[Hl HR]".
    - wp_cmpxchg_fail. iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
      wp_pures. iApply ("HΦ" $! false). done.
    - iDestruct "HR" as "[Hl2 HR]".
      iCombine "Hl Hl2" as "Hl".
      rewrite dfrac_op_own Qp.quarter_three_quarter.
      wp_cmpxchg_suc.
      iModIntro.
      iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
      iDestruct "Hl" as "[Hl1 Hl2]".
      iSplitL "Hl1"; first (iNext; iExists true; eauto).
      rewrite /locked. wp_pures.
      iApply "HΦ".
      eauto with iFrame.
  Qed.

  (** More general spec that allows a non-trivial namespace; rarely needed. *)
  Lemma wp_Mutex__Lock' stk E lk R :
    ↑N ⊆ E →
    {{{ is_lock lk R }}} Mutex__Lock lk @ stk; E {{{ RET #(); locked lk ∗ R }}}.
  Proof.
    iIntros (? Φ) "#Hl HΦ". iLöb as "IH". wp_rec.
    wp_apply (wp_Mutex__TryLock with "Hl"); auto. iIntros ([]).
    - iIntros "[Hlked HR]". wp_pures. iApply "HΦ"; by iFrame.
    - iIntros "_". wp_pures. iApply ("IH" with "[HΦ]"). auto.
  Qed.

  Lemma wp_Mutex__Lock lk R :
    {{{ is_lock lk R }}} Mutex__Lock lk {{{ RET #(); locked lk ∗ R }}}.
  Proof. eapply wp_Mutex__Lock'; auto. Qed.

  (** More general spec that allows a non-trivial namespace; rarely needed *)
  Lemma wp_Mutex__Unlock' stk E lk R :
    ↑N ⊆ E →
    {{{ is_lock lk R ∗ locked lk ∗ ▷ R }}} lock.release lk @ stk; E {{{ RET #(); True }}}.
  Proof.
    iIntros (? Φ) "(Hlock & Hlocked & HR) HΦ".
    iDestruct "Hlock" as (l ->) "#Hinv".
    rewrite /lock.release /=. wp_rec.
    wp_bind (CmpXchg _ _ _).
    iInv N as (b) "[>Hl _]".

    iDestruct (locked_loc with "Hlocked") as "Hl2".
    iDestruct (heap_pointsto_agree with "[$Hl $Hl2]") as %->.
    iCombine "Hl Hl2" as "Hl".
    rewrite dfrac_op_own Qp.quarter_three_quarter.
    wp_cmpxchg_suc.
    iModIntro.
    iSplitR "HΦ"; last by wp_pures; iApply "HΦ".
    iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
    iDestruct "Hl" as "[Hl1 Hl2]".
    iNext. iExists false. iFrame.
  Qed.

  Lemma wp_Mutex__Unlock lk R :
    {{{ is_lock lk R ∗ locked lk ∗ ▷ R }}} lock.release lk {{{ RET #(); True }}}.
  Proof. eapply wp_Mutex__Unlock'; auto. Qed.

  Lemma wp_Mutex__Unlock'' lk R :
    is_lock lk R -∗ {{{ locked lk ∗ ▷ R }}} lock.release lk {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hlock !# %Φ [??] HΦ". iApply (wp_Mutex__Unlock with "[-HΦ]"); by iFrame.
  Qed.

  (** cond var proofs *)

  Definition is_cond (c: loc) (lk : val) : iProp Σ :=
    heap_pointsto c DfracDiscarded lk.

  Global Instance is_cond_persistent c lk :
    Persistent (is_cond c lk) := _.

  Theorem wp_newCond' lk :
    {{{ is_free_lock lk }}}
      NewCond #lk
    {{{ (c: loc), RET #c; is_free_lock lk ∗ is_cond c #lk }}}.
  Proof.
    rewrite /is_cond.
    iIntros (Φ) "Hl HΦ".
    wp_rec. wp_pures.
    rewrite -wp_fupd.
    wp_apply wp_alloc_untyped; [ auto | ].
    iIntros (c) "Hc".
    iMod (heap_pointsto_persist with "Hc") as "Hcond".
    iModIntro.
    iApply "HΦ". by iFrame.
  Qed.

  Theorem wp_newCond lk R :
    {{{ is_lock lk R }}}
      NewCond lk
    {{{ (c: loc), RET #c; is_cond c lk }}}.
  Proof.
    rewrite /is_cond.
    iIntros (Φ) "Hl HΦ".
    wp_rec. wp_pures.
    rewrite -wp_fupd.
    iDestruct (is_lock_flat with "Hl") as %[l ->].
    wp_apply wp_alloc_untyped; [ auto | ].
    iIntros (c) "Hc".
    iMod (heap_pointsto_persist with "Hc") as "Hcond".
    iModIntro.
    by iApply "HΦ".
  Qed.

  Theorem wp_Cond__Signal c lk :
    {{{ is_cond c lk }}}
      Cond__Signal #c
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_rec. wp_pures.
    iApply ("HΦ" with "[//]").
  Qed.

  Theorem wp_Cond__Broadcast c lk :
    {{{ is_cond c lk }}}
      Cond__Broadcast #c
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_rec. wp_pures.
    iApply ("HΦ" with "[//]").
  Qed.

  Theorem wp_Cond__Wait c lk R :
    {{{ is_cond c lk ∗ is_lock lk R ∗ locked lk ∗ R }}}
      Cond__Wait #c
    {{{ RET #(); locked lk ∗ R }}}.
  Proof.
    iIntros (Φ) "(#Hcond&#Hlock&Hlocked&HR) HΦ".
    wp_rec. wp_pures.
    rewrite /is_cond.
    wp_untyped_load.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $HR]").
    wp_pures.
    wp_untyped_load.
    wp_apply (wp_Mutex__Lock with "[$Hlock]").
    iIntros "(Hlocked&HR)".
    iApply "HΦ".
    iFrame.
  Qed.

  Theorem wp_Cond__WaitTimeout c (t : u64) lk R :
    {{{ is_cond c lk ∗ is_lock lk R ∗ locked lk ∗ R }}}
      Cond__WaitTimeout #c #t
    {{{ RET #(); locked lk ∗ R }}}.
  Proof.
    iIntros (Φ) "Hpre HΦ".
    wp_rec. wp_pures.
    wp_apply (wp_Cond__Wait with "Hpre").
    done.
  Qed.

End proof.
End goose_lang.

#[global] Typeclasses Opaque is_lock is_cond locked.
