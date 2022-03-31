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
  ∃ (latch : loc),
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
    "#Hinvgc" ∷ mvcc_inv_gc γ ∗
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
  wp_loadField.
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
  (* TODO: Allocate [vchain_ptsto]. *)
  wp_apply wp_MkTuple; [done | admit |].
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
Admitted.

(*****************************************************************)
(* func MkIndex() *Index                                         *)
(*****************************************************************)
Theorem wp_MkIndex γ :
  mvcc_inv_gc γ -∗
  {{{ True }}}
    MkIndex #()
  {{{ (idx : loc), RET #idx; is_index idx γ }}}.
Proof.
  iIntros "#Hinvgc" (Φ) "!> _ HΦ".
  wp_call.

  (***********************************************************)
  (* idx := new(Index)                                       *)
  (***********************************************************)
  wp_apply (wp_allocStruct); first auto.
  iIntros (idx) "Hidx".
  iDestruct (struct_fields_split with "Hidx") as "Hidx".
  iNamed "Hidx".
  wp_pures.
  
  (***********************************************************)
  (* idx.buckets = make([]*IndexBucket, config.N_IDX_BUCKET) *)
  (***********************************************************)
  wp_apply (wp_new_slice); first auto.
  iIntros (bkts) "HbktsL".
  wp_storeField.
  
  (***********************************************************)
  (* for i := i := uint64(0); i < config.N_IDX_BUCKET; i++ { *)
  (*     b := new(IndexBucket)                               *)
  (*     b.latch = new(sync.Mutex)                           *)
  (*     b.m = make(map[uint64]*tuple.Tuple)                 *)
  (*     idx.buckets[i] = b                                  *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_ref_to); first auto.
  iIntros (iRef) "HiRef".
  wp_pures.
  iDestruct (is_slice_to_small with "HbktsL") as "HbktsS".
  wp_apply (wp_forUpto
              (λ n, (∃ bktsL, (is_slice_small bkts ptrT 1 (to_val <$> bktsL)) ∗
                              (⌜length bktsL = N_IDX_BUCKET⌝) ∗
                              ([∗ list] bkt ∈ (take (int.nat n) bktsL), is_index_bucket bkt γ)) ∗
                    (idx ↦[Index :: "buckets"] (to_val bkts)) ∗
                    ⌜True⌝)%I
              _ _ (U64 0) (U64 2048) with "[] [HbktsS $buckets $HiRef]"); first done.
  { clear Φ.
    iIntros (i Φ) "!> ((HbktsInv & Hidx & _) & HidxRef & %Hbound) HΦ".
    iDestruct "HbktsInv" as (bktsL) "(HbktsS & %Hlength & HbktsRP)".
    wp_pures.

    (* Allocating [IndexBucket]. *)
    wp_apply (wp_allocStruct); first auto.
    iIntros (bkt) "Hbkt".
    iDestruct (struct_fields_split with "Hbkt") as "Hbkt".
    iNamed "Hbkt".
    simpl.
    wp_pures.
    
    (* Allocating [Mutex]. *)
    wp_apply (wp_new_free_lock).
    iIntros (latch) "Hfree".
    wp_storeField.

    (* Allocating [map[uint64]*tuple.Tuple]. *)
    wp_apply (wp_NewMap).
    iIntros (m) "Hm".
    wp_storeField.

    wp_load.
    wp_loadField.
    assert (HboundNat : (int.nat i < length bktsL)%nat).
    { rewrite Hlength.
      rewrite /N_IDX_BUCKET.
      word.
    }
    wp_apply (wp_SliceSet with "[$HbktsS]").
    { iPureIntro.
      split; last auto.
      apply lookup_lt_is_Some.
      by rewrite fmap_length.
    }
    iIntros "HbktsS".
    wp_pures.
    iApply "HΦ".
    iMod (readonly_alloc_1 with "latch") as "#Hlatch".
    iMod (alloc_lock mvccN _ latch (own_index_bucket bkt γ) with "[$Hfree] [m Hm]") as "#Hlock".
    { eauto 10 with iFrame. }
    iModIntro.
    iFrame.
    rewrite -list_fmap_insert.
    iExists _.
    iFrame.
    rewrite insert_length.
    iSplit; first done.
    replace (int.nat (word.add i 1)) with (S (int.nat i)) by word.
    rewrite (take_S_r _ _ bkt); last by apply list_lookup_insert.
    iApply (big_sepL_app).
    iSplitL "HbktsRP".
    { by rewrite take_insert; last auto. }
    iApply (big_sepL_singleton).
    rewrite /is_index_bucket.
    eauto 10 with iFrame.
  }
  { iExists (replicate 2048 null).
    auto with iFrame.
  }
  iIntros "[(HbktsInv & Hidx & _) HiRef]".
  iDestruct "HbktsInv" as (bktsL) "(HbktsS & %Hlength & HbktsRP)".
  wp_pures.

  (***********************************************************)
  (* return idx                                              *) 
  (***********************************************************)
  iApply "HΦ".
  rewrite /is_index.
  do 2 iExists _.
  iMod (readonly_alloc_1 with "Hidx") as "$".
  iMod (readonly_alloc_1 with "HbktsS") as "$".
  iModIntro.
  iSplitL ""; first auto.
  iSplit; last auto.
  change (int.nat 2048) with 2048%nat.
  unfold N_IDX_BUCKET in Hlength.
  rewrite -Hlength.
  rewrite firstn_all.
  auto.
Qed.

End heap.
