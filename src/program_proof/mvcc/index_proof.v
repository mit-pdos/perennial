(* Import definitions/theorems of the Perennial framework with the disk FFI. *)
From Perennial.program_proof Require Export disk_prelude.
(* Import Coq model of our Goose program. *)
From Goose.github_com.mit_pdos.go_mvcc Require Import index.
From Perennial.program_proof.mvcc Require Import mvcc_ghost tuple_proof.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition own_index_bucket (bkt : loc) (γ : mvcc_names) : iProp Σ :=
  ∃ (lockm : loc) (lockmM : gmap u64 loc),
    "Hlockm" ∷ bkt ↦[IndexBucket :: "m"] #lockm ∗
    "HlockmOwn" ∷ is_map lockm 1 lockmM ∗
    "#HtuplesRP" ∷ ([∗ map] key ↦ tuple ∈ lockmM, is_tuple tuple key γ) ∗
    "_" ∷ True.
Local Hint Extern 1 (environments.envs_entails _ (own_index_bucket _ _)) => unfold own_index_bucket : core.
  
Definition is_index_bucket (bkt : loc) (γ : mvcc_names) : iProp Σ :=
  ∃ (latch : loc) (lockm : loc)
    (lockmM : gmap u64 loc),
    "#Hlatch" ∷ readonly (bkt ↦[IndexBucket :: "latch"] #latch) ∗
    "#HlatchRP" ∷ is_lock mvccN #latch (own_index_bucket bkt γ) ∗
    "_" ∷ True.

Definition N_IDX_BUCKET : nat := 2048.

Definition is_index (idx : loc) (γ : mvcc_names) : iProp Σ :=
  ∃ (bkts : Slice.t) (bktsL : list loc),
    "#Hbkts" ∷ readonly (idx ↦[Index :: "buckets"] (to_val bkts)) ∗
    (**
     * Goose seems to translate accessing slices of structs (via [SliceGet] or [SlicePut])
     * that have only one field to the type of that field, rather than the struct type.
     * So here we use [ptrT] instead of [structTy Index].
     *)
    "#HbktsL" ∷ readonly (is_slice_small bkts ptrT 1 (to_val <$> bktsL)) ∗
    "%HbktsLen" ∷ ⌜length bktsL = N_IDX_BUCKET⌝ ∗
    "#HbktsRP" ∷ ([∗ list] _ ↦ bkt ∈ bktsL, is_index_bucket bkt γ) ∗ 
    "_" ∷ True.

(*****************************************************************)
(* func (idx *Index) GetTuple(key uint64) *tuple.Tuple           *)
(*****************************************************************)
Theorem wp_index__GetTuple idx (key : u64) γ :
  is_index idx γ -∗
  {{{ True }}}
    Index__GetTuple #idx #key
  {{{ (tuple : loc), RET #tuple; is_tuple tuple key γ }}}.
Proof.
  iIntros "#Hindex !>" (Φ) "_ HΦ".
  iNamed "Hindex".
  wp_call.

  (***********************************************************)
  (* b := getBucket(key)                                     *)
  (* bucket := idx.buckets[b]                                *)
  (***********************************************************)
  wp_lam.
  wp_pures.
  wp_apply (wp_loadField_ro with "Hbkts").
  iMod (readonly_load with "HbktsL") as (q) "HbktsL'".
  list_elem bktsL (int.nat (word.modu key 2048)) as bkt.
  { revert HbktsLen. rewrite /N_IDX_BUCKET. word. }
  wp_apply (wp_SliceGet with "[$HbktsL']").
  { iPureIntro.
    rewrite list_lookup_fmap.
    by rewrite Hbkt_lookup.
  }
  iIntros "[HbktsL' _]".
  wp_pures.
  (* Q: What's the relationship between [Absorbing] and [Persistent]? *)
  iDestruct (big_sepL_lookup with "HbktsRP") as "HbktRP"; first done.
  iNamed "HbktRP".

  (***********************************************************)
  (* bucket.latch.Lock()                                     *)
  (* tupleCur, ok := bucket.m[key]                           *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "HlatchRP").
  iIntros "[Hlocked HbktOwn]".
  iNamed "HbktOwn".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapGet with "HlockmOwn").
  iIntros (tuple ok) "[%Hmap_get HlockmOwn]".
  wp_pures.
  
  (***********************************************************)
  (* if ok {                                                 *)
  (*     bucket.latch.Unlock()                               *)
  (*     return tupleCur                                     *)
  (* }                                                       *)
  (***********************************************************)
  wp_if_destruct.
  { (* The tuple is already in the index. *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    { eauto 10 with iFrame. }
    wp_pures.
    iApply "HΦ".
    iApply (big_sepM_lookup with "HtuplesRP").
    by apply map_get_true.
  }

  (***********************************************************)
  (* tupleNew := tuple.MkTuple()                             *)
  (* bucket.m[key] = tupleNew                                *)
  (* bucket.latch.Unlock()                                   *)
  (***********************************************************)
  apply map_get_false in Hmap_get as [Hlookup _].
  clear tuple.
  wp_apply wp_MkTuple.
  iIntros (tuple) "#HtupleRP".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapInsert with "HlockmOwn"); first done.
  iIntros "HlockmOwn".
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[-HΦ HtupleRP]").
  { iFrame "Hlocked HlatchRP".
    iNext.
    rewrite /own_index_bucket.
    do 2 iExists _.
    iFrame.
    iSplit; last done.
    iApply (big_sepM_insert with "[$HtuplesRP HtupleRP]"); first done.
    iFrame "HtupleRP".
  }
  wp_pures.
    
  (***********************************************************)
  (* return tupleNew                                         *)
  (***********************************************************)
  by iApply "HΦ".
Qed.

End heap.
