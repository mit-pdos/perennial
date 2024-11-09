From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.program_logic Require Import weakestpre.

From Perennial.goose_lang Require Import lang typing.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Export atomic.impl.
Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.

Section proof.
Context `{!heapGS Σ} (N : namespace).

#[local] Lemma uint64_pointsto (l: loc) (x: w64) :
  l ↦[uint64T] #x ⊣⊢ heap_pointsto l (DfracOwn 1) #x.
Proof.
  rewrite struct_pointsto_eq /struct_pointsto_def /=.
  rewrite loc_add_0 right_id.
  iSplit.
  - iIntros "[$ _]".
  - iIntros "$".
    iPureIntro. val_ty.
Qed.

#[local] Lemma uint32_pointsto (l: loc) (x: w32) :
  l ↦[uint32T] #x ⊣⊢ heap_pointsto l (DfracOwn 1) #x.
Proof.
  rewrite struct_pointsto_eq /struct_pointsto_def /=.
  rewrite loc_add_0 right_id.
  iSplit.
  - iIntros "[$ _]".
  - iIntros "$".
    iPureIntro. val_ty.
Qed.

Lemma wp_LoadUint64 (l: loc) (x: w64) stk E :
  {{{ ▷l ↦[uint64T] #x }}}
    atomic.LoadUint64 #l @ stk; E
  {{{ RET #x; l ↦[uint64T] #x }}}.
Proof.
  rewrite /atomic.LoadUint64.
  setoid_rewrite uint64_pointsto.
  iIntros (Φ) "Hl HΦ".
  wp_pures.
  wp_apply (wp_load with "[$Hl]"). iIntros "Hl".
  iApply "HΦ". iFrame.
Qed.

Lemma wp_LoadUint32 (l: loc) (x: w32) stk E :
  {{{ ▷l ↦[uint32T] #x }}}
    atomic.LoadUint32 #l @ stk; E
  {{{ RET #x; l ↦[uint32T] #x }}}.
Proof.
  rewrite /atomic.LoadUint32 /atomic.LoadUint64.
  setoid_rewrite uint32_pointsto.
  iIntros (Φ) "Hl HΦ".
  wp_pures.
  wp_apply (wp_load with "[$Hl]"). iIntros "Hl".
  iApply "HΦ". iFrame.
Qed.

Lemma wp_StoreUint64 (l: loc) (x0 x: w64) stk E :
  {{{ ▷l ↦[uint64T] #x0 }}}
    atomic.StoreUint64 #l #x @ stk; E
  {{{ RET #(); l ↦[uint64T] #x }}}.
Proof.
  rewrite /atomic.StoreUint64.
  setoid_rewrite uint64_pointsto.
  iIntros (Φ) "Hl HΦ".
  wp_pures.
  wp_apply (wp_atomic_store with "[$Hl]"). iIntros "Hl".
  iApply "HΦ". iFrame.
Qed.

Lemma wp_StoreUint32 (l: loc) (x0 x: w32) stk E :
  {{{ ▷l ↦[uint32T] #x0 }}}
    atomic.StoreUint32 #l #x @ stk; E
  {{{ RET #(); l ↦[uint32T] #x }}}.
Proof.
  rewrite /atomic.StoreUint32 /atomic.StoreUint64.
  setoid_rewrite uint32_pointsto.
  iIntros (Φ) "Hl HΦ".
  wp_pures.
  wp_apply (wp_atomic_store with "[$Hl]"). iIntros "Hl".
  iApply "HΦ". iFrame.
Qed.

End proof.
End goose_lang.
