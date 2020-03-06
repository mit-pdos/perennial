From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Export weakestpre.

From Perennial.goose_lang Require Export lang typing.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.goose_lang Require Import readonly.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Export lock.impl.
Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ext_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.

Local Coercion Var' (s:string): expr := Var s.

(** The CMRA we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitO) }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitO)].

Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapG Σ, !lockG Σ} (N : namespace).

  Definition lock_inv (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦ #b ∗ if b then True else own γ (Excl ()) ∗ R)%I.

  Definition is_lock (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ :=
    (∃ l: loc, ⌜lk = #l⌝ ∧ inv N (lock_inv γ l R))%I.

  Theorem is_lock_flat γ lk R :
    is_lock γ lk R -∗ ⌜∃ (l:loc), lk = #l⌝.
  Proof.
    iIntros "Hl"; iDestruct "Hl" as (l) "[-> _]"; eauto.
  Qed.

  Theorem is_lock_ty γ lk R :
    is_lock γ lk R -∗ ⌜val_ty lk lockRefT⌝.
  Proof.
    iIntros "Hlk".
    iDestruct (is_lock_flat with "Hlk") as (l) "->".
    iPureIntro.
    val_ty.
  Qed.

  Definition locked (γ : gname) : iProp Σ := own γ (Excl ()).

  Lemma locked_exclusive (γ : gname) : locked γ -∗ locked γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

  Global Instance lock_inv_ne γ l : NonExpansive (lock_inv γ l).
  Proof. solve_proper. Qed.
  Global Instance is_lock_ne γ l : NonExpansive (is_lock γ l).
  Proof. solve_proper. Qed.

  (** The main proofs. *)
  Global Instance is_lock_persistent γ l R : Persistent (is_lock γ l R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γ : Timeless (locked γ).
  Proof. apply _. Qed.

  Definition is_free_lock (l: loc): iProp Σ := l ↦ #false.

  Theorem is_free_lock_ty lk :
    is_free_lock lk -∗ ⌜val_ty #lk lockRefT⌝.
  Proof.
    iIntros "Hlk".
    iPureIntro.
    val_ty.
  Qed.

  Theorem alloc_lock E l R : is_free_lock l -∗ R ={E}=∗ ∃ γ, is_lock γ #l R.
  Proof.
    iIntros "Hl HR".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc N _ (lock_inv γ l R) with "[Hl HR Hγ]") as "#?".
    { iIntros "!>". iExists false. iFrame. }
    iModIntro.
    iExists γ, l.
    iSplit; eauto.
  Qed.

  Lemma wp_new_free_lock E:
    {{{ True }}} lock.new #() @ E {{{ lk, RET #lk; is_free_lock lk }}}.
  Proof using ext_tys.
    iIntros (Φ) "_ HΦ".
    wp_call.
    wp_apply wp_alloc_untyped; auto.
  Qed.

  Lemma newlock_spec E (R : iProp Σ):
    {{{ R }}} lock.new #() @ E {{{ lk γ, RET lk; is_lock γ lk R }}}.
  Proof using ext_tys.
    iIntros (Φ) "HR HΦ". rewrite -wp_fupd /lock.new /=.
    wp_lam. wp_apply wp_alloc_untyped; first by auto.
    iIntros (l) "Hl".
    iMod (alloc_lock with "Hl HR") as (γ) "Hlock".
    iModIntro.
    iApply "HΦ". iFrame.
  Qed.

  Lemma try_acquire_spec E γ lk R :
    ↑N ⊆ E →
    {{{ is_lock γ lk R }}} lock.try_acquire lk @ E
    {{{ b, RET #b; if b is true then locked γ ∗ R else True }}}.
  Proof.
    iIntros (? Φ) "#Hl HΦ". iDestruct "Hl" as (l ->) "#Hinv".
    wp_rec. wp_bind (CmpXchg _ _ _). iInv N as ([]) "[Hl HR]".
    - wp_cmpxchg_fail. iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
      wp_pures. iApply ("HΦ" $! false). done.
    - wp_cmpxchg_suc. iDestruct "HR" as "[Hγ HR]".
      iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
      rewrite /locked. wp_pures. by iApply ("HΦ" $! true with "[$Hγ $HR]").
  Qed.

  Lemma acquire_spec' E γ lk R :
    ↑N ⊆ E →
    {{{ is_lock γ lk R }}} lock.acquire lk @ E {{{ RET #(); locked γ ∗ R }}}.
  Proof.
    iIntros (? Φ) "#Hl HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_acquire_spec with "Hl"); auto. iIntros ([]).
    - iIntros "[Hlked HR]". wp_if. iApply "HΦ"; iFrame.
    - iIntros "_". wp_if. iApply ("IH" with "[HΦ]"). auto.
  Qed.

  Lemma acquire_spec γ lk R :
    {{{ is_lock γ lk R }}} lock.acquire lk {{{ RET #(); locked γ ∗ R }}}.
  Proof. eapply acquire_spec'; auto. Qed.

  Lemma release_spec' E γ lk R :
    ↑N ⊆ E →
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}} lock.release lk @ E {{{ RET #(); True }}}.
  Proof.
    iIntros (? Φ) "(Hlock & Hlocked & HR) HΦ".
    iDestruct "Hlock" as (l ->) "#Hinv".
    rewrite /lock.release /=. wp_lam.
    wp_bind (CmpXchg _ _ _).
    iInv N as (b) "[Hl _]".
    destruct b.
    - wp_cmpxchg_suc.
      iModIntro.
      iSplitR "HΦ"; last by wp_seq; iApply "HΦ".
      iNext. iExists false. by iFrame.
    - wp_cmpxchg_fail.
      iModIntro.
      iSplitR "HΦ"; last by wp_seq; iApply "HΦ".
      iNext. iExists false. by iFrame.
  Qed.

  Lemma release_spec γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}} lock.release lk {{{ RET #(); True }}}.
  Proof. eapply release_spec'; auto. Qed.

  (** cond var proofs *)

  Definition is_cond (c: loc) (lk : val) : iProp Σ :=
    c ↦ro lk.

  Theorem is_cond_dup c lk :
    is_cond c lk -∗ is_cond c lk ∗ is_cond c lk.
  Proof.
    iIntros "Hc".
    iDestruct "Hc" as "[Hc1 Hc2]".
    iSplitL "Hc1"; iFrame "#∗".
  Qed.

  Theorem wp_newCond γ lk R :
    {{{ is_lock γ lk R }}}
      lock.newCond lk
    {{{ c, RET #c; is_cond c lk }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    wp_call.
    iDestruct (is_lock_flat with "Hl") as %[l ->].
    wp_apply wp_alloc_untyped; [ auto | ].
    iIntros (c) "Hc".
    rewrite ptsto_ro_weaken.
    iApply "HΦ".
    iFrame.
  Qed.

  Theorem wp_condSignal c lk :
    {{{ is_cond c lk }}}
      lock.condSignal #c
    {{{ RET #(); is_cond c lk }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_call.
    iApply ("HΦ" with "[$Hc]").
  Qed.

  Theorem wp_condBroadcast c lk :
    {{{ is_cond c lk }}}
      lock.condBroadcast #c
    {{{ RET #(); is_cond c lk }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_call.
    iApply ("HΦ" with "[$]").
  Qed.

  Theorem wp_condWait γ c lk R :
    {{{ is_cond c lk ∗ is_lock γ lk R ∗ locked γ ∗ R }}}
      lock.condWait #c
    {{{ RET #(); is_cond c lk ∗ locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "(Hc&#Hlock&Hlocked&HR) HΦ".
    wp_call.
    iDestruct (ptsto_ro_load with "Hc") as (q) "Hc".
    wp_untyped_load.
    wp_apply (release_spec with "[$Hlock $Hlocked $HR]").
    wp_pures.
    wp_untyped_load.
    wp_apply (acquire_spec with "[$Hlock]").
    iIntros "(Hlocked&HR)".
    iApply "HΦ".
    iSplitR "Hlocked HR"; last by iFrame.
    iApply (ptsto_ro_from_q with "[$]").
  Qed.

End proof.
End goose_lang.

Typeclasses Opaque is_lock is_cond locked.
