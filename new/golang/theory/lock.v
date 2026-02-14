From New.proof Require Export proof_prelude.
From New.golang Require Export defn.lock.
From New.golang.theory Require Export pre.

From New.proof Require Export tok_set.

From New.experiments Require Export glob.
From Perennial Require Export base.

#[local] Transparent lock.trylock lock.lock lock.unlock.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.
Collection W := sem_fn + pre_sem.

(** This means [m] is a valid mutex with invariant [R]. *)
Definition is_lock (m: loc) (R : iProp Σ) : iProp Σ :=
  "#Hinv" ∷ inv nroot (
        ∃ b : bool,
          (m ↦{# 1/4} b) ∗
          if b then True else m ↦{# 3/4} b ∗ R
        ) ∗
  "_" ∷ True.
#[global] Opaque is_lock.
#[local] Transparent is_lock.

(** This resource denotes ownership of the fact that the lock is currently
    locked. *)
Definition own_lock (m: loc) : iProp Σ := m ↦{# 3/4} true.
#[global] Opaque own_lock.
#[local] Transparent own_lock.

Lemma own_lock_exclusive (m : loc) : own_lock m -∗ own_lock m -∗ False.
Proof.
  iIntros "H1 H2". rewrite /own_lock typed_pointsto_unseal.
  by iCombine "H1 H2" gives %[Hbad _].
Qed.

Global Instance is_lock_ne m : NonExpansive (is_lock m).
Proof. solve_proper. Qed.

(** The main proofs. *)
Global Instance is_lock_persistent m R : Persistent (is_lock m R).
Proof. apply _. Qed.
Global Instance locked_timeless m : Timeless (own_lock m).
Proof. apply _. Qed.

Theorem init_lock R E m : m ↦ false -∗ ▷ R ={E}=∗ is_lock m R.
Proof.
  iIntros "Hl HR".
  simpl.
  iNamed "Hl".
  simpl.
  iFrame "#".
  iMod (inv_alloc nroot _ (_) with "[Hl HR]") as "#?".
  2:{ by iFrame "#". }
  { iIntros "!>". iExists false. iFrame.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
    iDestruct "Hl" as "[$$]".
  }
Qed.

Lemma wp_lock_trylock m R :
  {{{ is_lock m R }}}
    lock.trylock #m
  {{{ (locked : bool), RET #locked; if locked then own_lock m ∗ R else True }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_bind (CmpXchg _ _ _).
  iInv nroot as ([]) "[Hl HR]".
  - wp_bind (CmpXchg _ _ _).
    iApply (wp_cmpxchg_fail (V:=bool) with "[$]").
    { done. }
    iNext.
    iIntros "Hl".
    iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
    wp_auto.
    by iApply "HΦ".
  - iDestruct "HR" as "[Hl2 HR]".
    iCombine "Hl Hl2" as "Hl".
    rewrite Qp.quarter_three_quarter.
    wp_bind (CmpXchg _ _ _).
    iApply (wp_cmpxchg_suc (V:=bool) with "[$]").
    { constructor. }
    iNext. iIntros "Hl".
    iModIntro.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
    iDestruct "Hl" as "[Hl1 Hl2]".
    iSplitL "Hl1"; first (iNext; iExists true; eauto).
    rewrite /locked. wp_auto.
    iApply "HΦ".
    eauto with iFrame.
Qed.

Lemma wp_lock_lock m R :
  {{{ is_lock m R }}}
    lock.lock #m
  {{{ RET #(); own_lock m ∗ R }}}.
Proof.
  iLöb as "IH".
  wp_start as "H". iNamed "H".
  wp_bind (CmpXchg _ _ _).
  iInv nroot as ([]) "[Hl HR]".
  - wp_bind (CmpXchg _ _ _).
    iApply (wp_cmpxchg_fail (V:=bool) with "[$]").
    { done. }
    iNext.
    iIntros "Hl".
    iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
    wp_auto.
    wp_apply "IH"; [iFrame "#" | iFrame].
  - iDestruct "HR" as "[Hl2 HR]".
    iCombine "Hl Hl2" as "Hl".
    rewrite Qp.quarter_three_quarter.
    wp_bind (CmpXchg _ _ _).
    iApply (wp_cmpxchg_suc (V:=bool) with "[$]").
    { constructor. }
    iNext. iIntros "Hl".
    iModIntro.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
    iDestruct "Hl" as "[Hl1 Hl2]".
    iSplitL "Hl1"; first (iNext; iExists true; eauto).
    rewrite /locked. wp_auto.
    iApply "HΦ".
    eauto with iFrame.
Qed.

Lemma wp_lock_unlock m R :
  {{{ is_lock m R ∗ own_lock m ∗ ▷ R }}}
    lock.unlock #m
  {{{ RET #(); True }}}.
Proof using W.
  wp_start as "(#His & Hlocked & HR)".
  iNamed "His".
  wp_bind (CmpXchg _ _ _).
  iInv nroot as (b) "[>Hl _]".

  unfold own_lock.
  iCombine "Hl Hlocked" gives %[=]. subst.
  iCombine "Hl Hlocked" as "Hl".
  rewrite Qp.quarter_three_quarter.
  wp_apply (wp_cmpxchg_suc with "[$]"); first done.
  iIntros "Hl".
  iModIntro.
  iSplitR "HΦ"; last by wp_auto; iApply "HΦ".
  iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
  iDestruct "Hl" as "[Hl1 Hl2]".
  iNext. iExists false. iFrame.
Qed.

End proof.
