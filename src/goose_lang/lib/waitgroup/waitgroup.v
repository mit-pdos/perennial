From iris.proofmode Require Import tactics.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.program_logic Require Import weakestpre.

(* From Perennial.goose_lang Require Import lang typing. *)
From Perennial.goose_lang Require Import proofmode notation.
(* From Perennial.goose_lang Require Import persistent_readonly. *)
From Perennial.goose_lang.lib Require Export waitgroup.impl.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Export lock.

From Perennial.program_proof.fencing Require Import map.
Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.

Local Coercion Var' (s:string): expr := Var s.

(*
  XXX:
  The waitgroup docs/comments stresses the fact that "the first WaitGroup.Add
  must be synchronized with WaitGroup.Wait". Why? I can't tell if it's a
  liveness issue, or safety. One conservative model would have a "positive" and
  a "negative" counter. Negative is increased each time Done() is called, and
  positive is increased when Add() is called. We can make access to the positive
  integer unguarded by a mutex, so concurrent Add() and Wait() is disallowed.
  This is overly conservative, since concurrent Add()s are also disallowed, as
  are concurrent Add() and Wait() when the counter is guaranteed to not be 0,
  which is allowed to happen.
 *)

Section proof.
  Context `{!heapGS Σ} (N : namespace).
  Context `{!mapG Σ u64 unit}.

  Implicit Type γ:gname.

  Definition own_WaitGroup_token γ (i:u64) : iProp Σ := i ⤳[γ] ().

  (* XXX: here, wg is a value. Maybe it should be a loc? *)
  Definition own_WaitGroup (wg:val) γ (n:u64) (P:u64 → iProp Σ) : iProp Σ :=
    ∃ lk (vptr:loc),
      ⌜wg = (lk, #vptr)%V⌝ ∗
      is_lock N lk (
        ∃ (remaining:gset u64) (total:u64),
          vptr ↦[uint64T] #(size remaining) ∗
          ([∗ set] i ∈ (fin_to_set u64), ⌜i ∈ remaining⌝ ∨ own_WaitGroup_token γ i) ∗
          ([∗ set] i ∈ (fin_to_set u64), ⌜int.nat i ≥ int.nat total⌝ ∨ ⌜i ∈ remaining⌝ ∨ (□ (P i)))
      ).

Lemma wp_NewWaitGroup (P:u64 → iProp Σ) :
  {{{
      True
  }}}
    waitgroup.New #()
  {{{
        (wg:val) γ, RET wg; own_WaitGroup wg γ 0 P
  }}}
.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply (wp_new_free_lock).
  iIntros (lk) "His_lock".
  wp_apply (wp_ref_to).
  { naive_solver. }
  iIntros (vptr) "Hv".
  wp_pures.

  iMod (ghost_map_alloc_fin ()) as (tok_gn) "Htokens".
  iApply "HΦ".
  iExists _, _.
  iSplitL ""; first done.
  iMod (alloc_lock with "His_lock [-]") as "$"; last done.
  iNext.
  iExists ∅, (U64 0).
  rewrite size_empty.
  iFrame "Hv".
  iSplitR "".
  {
    iApply (big_sepS_impl with "Htokens").
    iModIntro.
    iIntros.
    iRight.
    iFrame.
  }
  {
    iDestruct (big_sepS_emp with "[]") as "Htriv"; first done.
    iApply (big_sepS_impl with "Htriv").
    iModIntro.
    iIntros.
    iLeft.
    iPureIntro.
    word.
  }
Qed.

Local Opaque load_ty store_ty.

Lemma wp_WaitGroup__Add wg γ n P :
int.nat (word.add n 1) > int.nat n →
  {{{
      own_WaitGroup wg γ n P
  }}}
    waitgroup.Add wg #1
  {{{
        RET #(); own_WaitGroup wg γ (word.add n 1) P ∗ own_WaitGroup_token γ n
  }}}.
Proof.
  intros Hoverflow.
  iIntros (Φ) "Hwg HΦ".
  wp_call.
  iDestruct "Hwg" as (??) "[%HwgPair #Hlk]".
  rewrite HwgPair.
  wp_pures.
  wp_apply (acquire_spec with "Hlk").
  iIntros "[Hlocked Hown]".
  wp_pures.
  iDestruct "Hown" as (remaining total) "(Hv & Htoks & HP)".
  wp_load.
  wp_store.
Admitted.

End proof.
End goose_lang.
