From New.proof Require Export proof_prelude.
From New.golang Require Export defn.lock.
From New.proof Require Export tok_set.
From New.experiments Require Export glob.
From Perennial Require Export base.

#[local] Transparent lock.trylock lock.lock lock.unlock.

Section proof.
Context `{heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

(** This means [m] is a valid mutex with invariant [R] in namespace [N]. *)
Definition is_lockN (N: namespace) (m: loc) (R : iProp Σ) : iProp Σ :=
  "#Hinv" ∷ inv N (
        ∃ b : bool,
          (m ↦{# 1/4} b) ∗
          if b then True else m ↦{# 3/4} b ∗ R
        ) ∗
  "_" ∷ True.
#[global] Opaque is_lockN.
#[local] Transparent is_lockN.


(** This resource denotes ownership of the fact that the lock is currently locked. *)
Definition own_lockN (m: loc) : iProp Σ := m ↦{# 3/4} true.
#[global] Opaque own_lockN.
#[local] Transparent own_lockN.

Lemma own_lock_exclusive (m : loc) : own_lockN m -∗ own_lockN m -∗ False.
Proof.
  iIntros "H1 H2".
  iCombine "H1 H2" gives %[Hbad _].
  exfalso.
  rewrite go_type_size_unseal in Hbad. naive_solver.
Qed.


Global Instance is_lockN_ne m N : NonExpansive (is_lockN N m).
Proof. solve_proper. Qed.

Global Instance is_lockN_persistent m N R : Persistent (is_lockN N m R).
Proof. apply _. Qed.


(** Allocate the invariant in an arbitrary namespace [N]. *)
Theorem init_lockN R E N m :
  m ↦ false -∗ ▷ R ={E}=∗ is_lockN N m R.
Proof.
  iIntros "Hl HR".
  iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
iDestruct "Hl" as "[Hl Hr]".  (* now Hl : m ↦{#1/4} false *)
  iMod (inv_alloc N _ (∃ b:bool, m ↦{#1/4} b ∗ (if b then True else m ↦{#3/4} b ∗ R))
          with "[Hl HR Hr]") as "#Hinv".
  { iNext. iExists false. iSplitL "Hl".

    -
 iExact "Hl".
    - iFrame. }
  iModIntro. iFrame "#".
Qed.


Lemma wp_lock_lock N m R :
  {{{ is_lockN N m R }}}
    lock.lock #m
  {{{ RET #(); own_lockN m ∗ R }}}.
Proof.
    iLöb as "IH".
  wp_start as "H". wp_call. iNamed "H".
  wp_bind (CmpXchg _ _ _).
  iInv N as ([]) "[Hl HR]".
  - wp_bind (CmpXchg _ _ _).
    iApply (wp_typed_cmpxchg_fail (V:=bool) with "[$]").
    { done. }
    { naive_solver. }
    iNext.
    iIntros "Hl".
    iModIntro. iSplitL "Hl"; first (iNext; iExists true; eauto).
    wp_auto.
    wp_apply "IH"; [iFrame "#" | iFrame].
  - iDestruct "HR" as "[Hl2 HR]".
    iCombine "Hl Hl2" as "Hl".
    rewrite Qp.quarter_three_quarter.
    wp_bind (CmpXchg _ _ _).
    iApply (wp_typed_cmpxchg_suc (V:=bool) with "[$]").
    { constructor. }
    { done. }
    iNext. iIntros "Hl".
    iModIntro.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
    iDestruct "Hl" as "[Hl1 Hl2]".
    iSplitL "Hl1"; first (iNext; iExists true; eauto).
    rewrite /locked. wp_auto.
    iApply "HΦ".
    eauto with iFrame.
Qed.


Lemma wp_lock_unlock N m R :
  {{{ is_lockN N m R ∗ own_lockN m ∗ ▷ R }}}
    lock.unlock #m
  {{{ RET #(); True }}}.
Proof.
    wp_start as "(#His & Hlocked & HR)". wp_call.
  iNamed "His".
  wp_bind (CmpXchg _ _ _).
  iInv N as (b) "[>Hl _]".

  unfold own_lockN.
  iCombine "Hl Hlocked" gives %[_ [=]]. subst.
  iCombine "Hl Hlocked" as "Hl".
  rewrite Qp.quarter_three_quarter.
  iApply (wp_typed_cmpxchg_suc (V:=bool) with "[$]").
  { econstructor. }
  { econstructor. }
  iIntros "!# Hl".
  iModIntro.
  iSplitR "HΦ"; last by wp_auto; iApply "HΦ".
  iEval (rewrite -Qp.quarter_three_quarter) in "Hl".
  iDestruct "Hl" as "[Hl1 Hl2]".
  iNext. iExists false. iFrame.
Qed.

End proof.
