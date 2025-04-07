From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.program_logic Require Export weakestpre.

From Perennial.goose_lang Require Export lang typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode notation crash_borrow.
From Perennial.goose_lang Require Import persistent_readonly.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Export rwlock.impl.
From Perennial.goose_lang.lib Require Export rwlock.rwlock_noncrash.
Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.

Section proof.
  Context `{!heapGS Σ} (N : namespace).
  Context `{!stagedG Σ}.

  Definition is_crash_rwlock lk R Rc :=
    is_rwlock N lk (λ q, crash_borrow (R q) (Rc q)).

  (** The main proofs. *)
  Global Instance is_crash_rwlock_persistent l R Rc : Persistent (is_crash_rwlock l R Rc).
  Proof. apply _. Qed.

  Definition is_free_lock (l: loc): iProp Σ := heap_pointsto l (DfracOwn 1) #1 ∗ later_tok ∗ later_tok ∗ later_tok ∗ later_tok.

  Theorem is_free_lock_ty lk :
    is_free_lock lk -∗ ⌜val_ty #lk ptrT⌝.
  Proof.
    iIntros "Hlk".
    iPureIntro.
    val_ty.
  Qed.

  Theorem alloc_lock E l R Rc :
    □ (∀ q1 q2, R (q1 + q2)%Qp ∗-∗ R q1 ∗ R q2) -∗
    □ (∀ q1 q2, Rc (q1 + q2)%Qp ∗-∗ Rc q1 ∗ Rc q2) -∗
    □ (∀ q, R q -∗ Rc q) -∗
    heap_pointsto l (DfracOwn 1) #1 -∗ crash_borrow (R 1%Qp) (Rc 1%Qp) ={E}=∗ is_crash_rwlock #l R Rc.
  Proof.
    iIntros "#H1 #H2 #H3 Hl HR".
    iMod (alloc_lock N E l (λ q, (crash_borrow (R q) (Rc q))) with "[] [] [$] [$]").
    { iModIntro. iIntros (q1 q2) "H".
      iApply (crash_borrow_split_post with "H").
      { iNext. iIntros "HR". iApply "H1"; eauto. }
      { eauto. }
      { eauto. }
      { iNext. iIntros "HR". iApply "H2"; eauto. }
    }
    { iModIntro. iIntros (q1 q2) "Hc1 Hc2".
      iApply (crash_borrow_combine_post with "Hc1 Hc2").
      { iNext. eauto. }
      { iNext. iIntros "HR". iApply "H2"; eauto. }
      { iNext. iIntros "HR". iApply "H1"; eauto. }
    }
    eauto.
  Qed.

  Lemma wp_new_free_lock:
    {{{ True }}} newRWMutex #() {{{ lk, RET #lk; is_free_lock lk }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec. wp_pures.
    iApply wp_crash_borrow_generate_pre; first auto.
    wp_apply wp_alloc_untyped; auto.
    iIntros (?) "Hl Htoks".
    iApply "HΦ". iFrame.
 Qed.

  Lemma alloc_rwlock Φ Φc e lk (R Rc : Qp → iProp Σ):
    □ (∀ q1 q2, R (q1 + q2)%Qp ∗-∗ R q1 ∗ R q2) -∗
    □ (∀ q1 q2, Rc (q1 + q2)%Qp ∗-∗ Rc q1 ∗ Rc q2) -∗
    □ (∀ q, R q -∗ Rc q) -∗
    R 1%Qp ∗
    is_free_lock lk ∗
    (is_crash_rwlock #lk R Rc -∗
          WPC e @ ⊤ {{ Φ }} {{ Rc 1%Qp -∗ Φc }}) -∗
    WPC e @ ⊤ {{ Φ }} {{ Φc }}.
  Proof.
    clear.
    iIntros "#Hwand1 #Hwand2 #Hwand3 (HR&Hfree&Hwp)".
    iDestruct "Hfree" as "(Hfree1&Htoks)".
    iApply (wpc_crash_borrow_inits with "[$] HR []").
    { iModIntro. iApply "Hwand3". }
    iIntros "Hborrow".
    iMod (alloc_lock with "[] [] [] [$] Hborrow") as "H"; try eauto.
    iApply "Hwp". eauto.
  Qed.


  Lemma read_wp_Mutex__Lock lk R Rc :
    {{{ is_crash_rwlock lk R Rc }}} RWMutex__RLock lk {{{ RET #(); crash_borrow (R rfrac) (Rc rfrac) }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ".
    wp_apply (read_wp_Mutex__Lock with "[$]").
    eauto.
  Qed.

  Lemma read_wp_Mutex__Unlock lk R Rc :
    {{{ is_crash_rwlock lk R Rc ∗ crash_borrow (R rfrac) (Rc rfrac) }}}
      RWMutex__RUnlock lk
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(Hlock&Hborrow) HΦ".
    wp_apply (read_wp_Mutex__Unlock with "[$Hlock $Hborrow]").
    iApply "HΦ"; eauto.
  Qed.

  Lemma write_wp_Mutex__Lock lk R Rc :
    {{{ is_crash_rwlock lk R Rc }}}
      RWMutex__Lock lk
    {{{ RET #(); wlocked lk ∗ crash_borrow (R 1%Qp) (Rc 1%Qp) }}}.
  Proof.
    iIntros (Φ) "Hlock HΦ".
    wp_apply (write_wp_Mutex__Lock with "[$Hlock]").
    iApply "HΦ"; eauto.
  Qed.

  Lemma wp_Mutex__Unlock lk R Rc :
    {{{ is_crash_rwlock lk R Rc ∗ wlocked lk ∗ crash_borrow (R 1%Qp) (Rc 1%Qp) }}}
      RWMutex__Unlock lk
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(Hlock&Hborrow) HΦ".
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hborrow]").
    iApply "HΦ"; eauto.
  Qed.

End proof.
End goose_lang.

Typeclasses Opaque is_rwlock.
