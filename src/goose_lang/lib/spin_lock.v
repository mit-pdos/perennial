From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From iris.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Export lang.
From Perennial.goose_lang Require Import proofmode basic_triples notation.
From Perennial.goose_lang.lib Require Import lock.
Set Default Proof Using "Type".

Section goose_lang.
  Context `{ffi_sem: ext_semantics}.
  Context `{!ffi_interp ffi}.
  Context {ext_tys: ext_types ext}.

  Definition Var' s : @expr ext := Var s.
  Local Coercion Var' : string >-> expr.

Definition newlock : val := λ: <>, ref #false.
Definition try_acquire : val := λ: "l", CAS "l" #false #true.
Definition acquire : val :=
  rec: "acquire" "l" := if: try_acquire "l" then #() else "acquire" "l".
Definition release : val := λ: "l", CmpXchg "l" #true #false;; #().

(** The CMRA we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitO) }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitO)].

Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapG Σ, !lockG Σ} (N : namespace).

  Definition lock_inv (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦ Free #b ∗ if b then True else own γ (Excl ()) ∗ R)%I.

  Definition is_lock (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ :=
    (∃ l: loc, ⌜lk = #l⌝ ∧ inv N (lock_inv γ l R))%I.

  Theorem is_lock_flat γ lk R :
    is_lock γ lk R -∗ ⌜∃ (l:loc), lk = #l⌝.
  Proof.
    iIntros "Hl"; iDestruct "Hl" as (l) "[-> _]"; eauto.
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

  Definition is_free_lock (l: loc): iProp Σ := l ↦[boolT] #false.

  Theorem alloc_lock l R : is_free_lock l -∗ R ={⊤}=∗ ∃ γ, is_lock γ #l R.
  Proof.
    iIntros "Hl HR".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc N _ (lock_inv γ l R) with "[Hl HR Hγ]") as "#?".
    { iIntros "!>". iExists false. iFrame.
      iDestruct "Hl" as "[[Hl _] %]".
      rewrite loc_add_0.
      by iFrame. }
    iModIntro.
    iExists γ, l.
    iSplit; eauto.
  Qed.

  Lemma newlock_spec (R : iProp Σ):
    {{{ R }}} newlock #() {{{ lk γ, RET lk; is_lock γ lk R }}}.
  Proof using ext_tys.
    iIntros (Φ) "HR HΦ". rewrite -wp_fupd /newlock /=.
    wp_lam. wp_apply wp_alloc. (* TODO: to restore wp_alloc tactic, need a
    type hint in the code *)
    { val_ty. }
    iIntros (l) "Hl".
    iMod (alloc_lock with "Hl HR") as (γ) "Hlock".
    iModIntro.
    iApply "HΦ". iFrame.
  Qed.

  Lemma try_acquire_spec γ lk R :
    {{{ is_lock γ lk R }}} try_acquire lk
    {{{ b, RET #b; if b is true then locked γ ∗ R else True }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ". iDestruct "Hl" as (l ->) "#Hinv".
    wp_rec. wp_bind (CmpXchg _ _ _). iInv N as ([]) "[Hl HR]".
    - wp_cmpxchg_fail. iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
      wp_pures. iApply ("HΦ" $! false). done.
    - wp_cmpxchg_suc. iDestruct "HR" as "[Hγ HR]".
      iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
      rewrite /locked. wp_pures. by iApply ("HΦ" $! true with "[$Hγ $HR]").
  Qed.

  Lemma acquire_spec γ lk R :
    {{{ is_lock γ lk R }}} acquire lk {{{ RET #(); locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_acquire_spec with "Hl"). iIntros ([]).
    - iIntros "[Hlked HR]". wp_if. iApply "HΦ"; iFrame.
    - iIntros "_". wp_if. iApply ("IH" with "[HΦ]"). auto.
  Qed.

  Lemma release_spec γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}} release lk {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(Hlock & Hlocked & HR) HΦ".
    iDestruct "Hlock" as (l ->) "#Hinv".
    rewrite /release /=. wp_lam.
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
End proof.
End goose_lang.

Typeclasses Opaque is_lock locked.

Canonical Structure spin_lock `{ffi_sem: ext_semantics} `{!ffi_interp ffi} {ext_tys:ext_types ext} `{!heapG Σ, !lockG Σ} : lock Σ :=
  {| lock.locked_exclusive := locked_exclusive; lock.newlock_spec := newlock_spec;
     lock.acquire_spec := acquire_spec; lock.release_spec := release_spec |}.
