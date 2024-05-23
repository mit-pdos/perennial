From Perennial.program_proof.mvcc Require Import
     mvcc_prelude mvcc_ghost mvcc_inv mvcc_misc
     tuple_repr tuple_mk tuple_remove_versions.
From Goose.github_com.mit_pdos.vmvcc Require Import index.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition N_IDX_BUCKET : Z := 8192.
Definition hash_modu (key : u64) : nat :=
  uint.nat (word.modu (word.add (word.sru key 52) key) N_IDX_BUCKET).

Definition keys_hashed (hash : nat) :=
  filter (λ x, hash_modu x = hash) keys_all.

Definition own_index_bucket (bkt : loc) (hash : nat) (γ : mvcc_names) : iProp Σ :=
  ∃ (lockm : loc) (lockmM : gmap u64 loc),
    "Hlockm" ∷ bkt ↦[IndexBucket :: "m"] #lockm ∗
    "HlockmOwn" ∷ own_map lockm (DfracOwn 1) lockmM ∗
    "Hvchains" ∷ ([∗ set] key ∈ ((keys_hashed hash) ∖ (dom lockmM)), ptuple_auth γ (1/2) key [Nil; Nil]) ∗
    "#HtuplesRP" ∷ ([∗ map] key ↦ tuple ∈ lockmM, is_tuple tuple key γ) ∗
    "_" ∷ True.

#[local]
Hint Extern 1 (environments.envs_entails _ (own_index_bucket _ _ _)) => unfold own_index_bucket : core.
  
Definition is_index_bucket (bkt : loc) (hash : nat) (γ : mvcc_names) : iProp Σ :=
  ∃ (latch : loc),
    "#Hlatch" ∷ readonly (bkt ↦[IndexBucket :: "latch"] #latch) ∗
    "#HlatchRP" ∷ is_lock mvccN #latch (own_index_bucket bkt hash γ) ∗
    "_" ∷ True.

Definition is_index (idx : loc) (γ : mvcc_names) : iProp Σ :=
  ∃ (bkts : Slice.t) (bktsL : list loc) (p : proph_id),
    "#Hbkts" ∷ readonly (idx ↦[Index :: "buckets"] (to_val bkts)) ∗
    (**
     * Goose seems to translate accessing slices of structs (via [SliceGet] or [SlicePut])
     * that have only one field to the type of that field, rather than the struct type.
     * So here we use [ptrT] instead of [structTy Index].
     *)
    "#HbktsL" ∷ readonly (own_slice_small bkts ptrT (DfracOwn 1) (to_val <$> bktsL)) ∗
    "%HbktsLen" ∷ ⌜Z.of_nat (length bktsL) = N_IDX_BUCKET⌝ ∗
    "#HbktsRP" ∷ ([∗ list] i ↦ bkt ∈ bktsL, is_index_bucket bkt i γ) ∗
    "#Hinvgc" ∷ mvcc_inv_gc γ ∗
    "#Hinv" ∷ mvcc_inv_sst γ p ∗
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
  list_elem bktsL (hash_modu key) as bkt.
  { revert HbktsLen. rewrite /hash_modu /N_IDX_BUCKET. word. }
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
    { eauto 10 with iFrame . }
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
  (* Take [ptuple_auth] from [Hvchains]. *)
  (* iDestruct (big_sepS_delete with "[Hvchains]") as "H". *)
  rewrite (big_sepS_delete _ _ key); last first.
  { unfold keys_hashed.
    rewrite -not_elem_of_dom in Hlookup.
    apply elem_of_difference.
    split; last done.
    rewrite elem_of_filter.
    split; [auto | set_solver].
  }
  iDestruct "Hvchains" as "[Hvchain Hvchains]".
  wp_apply (wp_MkTuple with "Hinvgc Hinv Hvchain").
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
    iSplit.
    { rewrite dom_insert_L.
      iApply (big_sepS_subseteq with "Hvchains").
      set_solver.
    }
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

(*****************************************************************)
(* func (idx *Index) getKeys() []uint64                          *)
(*                                                               *)
(* Notes:                                                        *)
(* This function is only used by GC, which is a no-op, so we're  *)
(* simply proving trivial spec for safety here.                  *)
(*****************************************************************)
#[local]
Theorem wp_index__getKeys idx γ :
  is_index idx γ -∗
  {{{ True }}}
    Index__getKeys #idx
  {{{ (keysS : Slice.t) (keys : list u64), RET (to_val keysS);
      own_slice keysS uint64T (DfracOwn 1) (to_val <$> keys)
  }}}.
Proof.
  iIntros "#Hidx" (Φ) "!> _ HΦ".
  wp_call.

  (***********************************************************)
  (* var keys []uint64                                       *)
  (* keys = make([]uint64, 0, 2000)                          *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first done.
  iIntros (keysR) "HkeysR".
  wp_pures.
  wp_apply wp_new_slice_cap; [done | word |].
  iIntros (ptr) "HkeysS".
  wp_store.

  (***********************************************************)
  (* for _, bkt := range idx.buckets {                       *)
  (*     bkt.latch.Lock()                                    *)
  (*     for k := range bkt.m {                              *)
  (*         keys = append(keys, k)                          *)
  (*     }                                                   *)
  (*     bkt.latch.Unlock()                                  *)
  (* }                                                       *)
  (***********************************************************)
  iNamed "Hidx".
  wp_loadField.
  iMod (readonly_load with "HbktsL") as (q) "HbktsS".
  iDestruct (own_slice_small_sz with "HbktsS") as "%HbktsSz".
  rewrite fmap_length in HbktsSz.
  set P := (λ (_ : u64), ∃ keysS (keys : list u64),
               "HkeysR" ∷ keysR ↦[slice.T uint64T] (to_val keysS) ∗
               "HkeysS" ∷ own_slice keysS uint64T (DfracOwn 1) (to_val <$> keys))%I.
  wp_apply (wp_forSlice P _ _ _ _ _ (to_val <$> bktsL) with "[] [HkeysR HkeysS $HbktsS]").
  { (* Outer loop body. *)
    clear Φ.
    iIntros (i x Φ) "!> (HP & %Hbound & %Hlookup) HΦ".
    subst P. simpl.
    iNamed "HP".
    wp_pures.
    list_elem bktsL (uint.nat i) as bkt.
    iDestruct (big_sepL_lookup with "HbktsRP") as "HbktRP"; first apply Hbkt_lookup.
    iNamed "HbktRP".
    rewrite list_lookup_fmap Hbkt_lookup in Hlookup.
    inversion Hlookup.
    wp_loadField.
    wp_apply (acquire_spec with "HlatchRP").
    iIntros "[Hlocked Hbkt]".
    wp_pures.
    iNamed "Hbkt".
    wp_loadField.
    set P := (∃ keysS (keys : list u64),
                 "HkeysR" ∷ keysR ↦[slice.T uint64T] (to_val keysS) ∗
                 "HkeysS" ∷ own_slice keysS uint64T (DfracOwn 1) (to_val <$> keys))%I.
    wp_apply (wp_MapIter _ _ _ _ _ P (λ _ _, True)%I (λ _ _, True)%I
               with "HlockmOwn [HkeysR HkeysS]"); [ | done | |].
    { (* Inner loop entry. *) subst P. eauto with iFrame. }
    { (* Inner loop body. *)
      clear Φ.
      iIntros (k tpl Φ) "!> [HP _] HΦ".
      clear keysS keys.
      iNamed "HP".
      wp_load.
      wp_apply (wp_SliceAppend with "[$HkeysS]"); [done | by auto |].
      iIntros (keysS') "HkeysS".
      wp_store.
      iApply "HΦ".
      subst P. simpl.
      rewrite -fmap_snoc.
      eauto with iFrame.
    }
    iIntros "[HlockmOwn [HP _]]".
    subst P. simpl.
    iNamed "HP".
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[- HΦ HkeysR HkeysS]").
    { (* Re-establish bucket lock invariant. *) eauto 10 with iFrame. }
    iApply "HΦ".
    eauto with iFrame.
  }
  { (* Outer loop entry. *)
    subst P. simpl.
    iExists _, [].
    iFrame.
  }
  iIntros "[HP _]".
  subst P. simpl. iNamed "HP".
  wp_pures.

  (***********************************************************)
  (* return keys                                             *)
  (***********************************************************)
  wp_load.
  by iApply "HΦ".
Qed.

(*****************************************************************)
(* func (idx *Index) DoGC(tidMin uint64)                         *)
(*****************************************************************)
Theorem wp_index__DoGC idx (tidmin : u64) γ :
  is_index idx γ -∗
  min_tid_lb γ (uint.nat tidmin) -∗
  {{{ True }}}
    Index__DoGC #idx #tidmin
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Hidx #Hminlb" (Φ) "!> _ HΦ".
  wp_call.

  (***********************************************************)
  (* keys := idx.getKeys()                                   *)
  (***********************************************************)
  wp_apply (wp_index__getKeys with "Hidx").
  iIntros (keysS keys) "HkeysS".
  wp_pures.

  (***********************************************************)
  (* for _, k := range keys {                                *)
  (*     tuple := idx.GetTuple(k)                            *)
  (*     tuple.RemoveVersions(tidMin)                        *)
  (* }                                                       *)
  (***********************************************************)
  iDestruct (own_slice_to_small with "HkeysS") as "HkeysS".
  wp_apply (wp_forSlice (λ _, True)%I _ _ _ _ _ (to_val <$> keys) with "[] [HkeysS]").
  { (* Loop body. *)
    clear Φ.
    iIntros (i x Φ) "!> (_ & %Hbound & %Hlookup) HΦ".
    apply list_lookup_fmap_inv in Hlookup.
    destruct Hlookup as (k & Hval & Hlookup).
    subst x.
    wp_pures.
    wp_apply (wp_index__GetTuple with "Hidx").
    iIntros (tpl) "#Htpl".
    wp_pures.
    wp_apply (wp_tuple__RemoveVersions with "Htpl Hminlb").
    by iApply "HΦ".
  }
  { (* Loop entry. *) iSplit; done. }
  iIntros "_".
  wp_pures.
  by iApply "HΦ".
Qed.

#[local]
Lemma filter_subseteq_union_S (s : gset u64) (f : u64 -> nat) (n : nat) :
  (filter (λ x, S n ≤ f x)%nat s) ∪ (filter (λ x, f x = n)%nat s) ⊆ filter (λ x, n ≤ f x)%nat s.
Proof.
  apply elem_of_subseteq.
  intros x.
  rewrite elem_of_union.
  do 3 rewrite elem_of_filter.
  intros [[Hle Hin] | [Heq Hin]]; auto with lia.
Qed.

#[local]
Lemma filter_all (P : u64 -> Prop) {H : ∀ x, Decision (P x)} (s : gset u64) :
  (∀ x, P x) ->
  s = filter P s.
Proof. set_solver. Qed.
  
(*****************************************************************)
(* func MkIndex() *Index                                         *)
(*****************************************************************)
Theorem wp_MkIndex γ p :
  mvcc_inv_gc γ -∗
  mvcc_inv_sst γ p -∗
  {{{ [∗ set] key ∈ keys_all, ptuple_auth γ (1/2) key [Nil; Nil] }}}
    MkIndex #()
  {{{ (idx : loc), RET #idx; is_index idx γ }}}.
Proof.
  iIntros "#Hinv #Hinvgc" (Φ) "!> Hvchains HΦ".
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
  iDestruct (own_slice_to_small with "HbktsL") as "HbktsS".
  wp_apply (wp_forUpto
              (λ n, (∃ bktsL, (own_slice_small bkts ptrT (DfracOwn 1) (to_val <$> bktsL)) ∗
                              (⌜Z.of_nat (length bktsL) = N_IDX_BUCKET⌝) ∗
                              ([∗ list] i ↦ bkt ∈ (take (uint.nat n) bktsL), is_index_bucket bkt i γ)) ∗
                    (idx ↦[Index :: "buckets"] (to_val bkts)) ∗
                    ([∗ set] key ∈ filter (λ x, (uint.nat n) ≤ hash_modu x)%nat keys_all, ptuple_auth γ (1/2) key [Nil; Nil]) ∗
                    ⌜True⌝)%I
              _ _ (W64 0) (W64 N_IDX_BUCKET) with "[] [HbktsS Hvchains $buckets $HiRef]"); first done.
  { clear Φ.
    iIntros (i Φ) "!> ((HbktsInv & Hidx & Hvchains & _) & HidxRef & %Hbound) HΦ".
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
    unfold N_IDX_BUCKET in *.
    wp_apply (wp_SliceSet with "[$HbktsS]").
    { iPureIntro.
      split; last auto.
      apply lookup_lt_is_Some.
      rewrite fmap_length. word.
    }
    iIntros "HbktsS".
    wp_pures.
    iApply "HΦ".
    iMod (readonly_alloc_1 with "latch") as "#Hlatch".
    rewrite big_sepS_subseteq; last first.
    { apply filter_subseteq_union_S. }
    rewrite big_sepS_union; last first.
    { apply elem_of_disjoint.
      intros x.
      do 2 rewrite elem_of_filter.
      lia.
    }
    iDestruct "Hvchains" as "[Hvchains Hvchain]".
    iMod (alloc_lock mvccN _ latch (own_index_bucket bkt (uint.nat i) γ) with "[$Hfree] [m Hm Hvchain]") as "#Hlock".
    { iNext.
      iExists _, _.
      iFrame.
      iSplitL "Hvchain"; last auto.
      rewrite dom_empty_L difference_empty_L.
      by iApply "Hvchain".
    }
    iModIntro.
    iFrame.
    rewrite -list_fmap_insert.
    iSplitR "Hvchains"; last first.
    { iSplit; last done.
      by replace (uint.nat (word.add _ _))%nat with (S (uint.nat i))%nat; last word.
    }
    iExists _.
    iFrame.
    rewrite insert_length.
    iSplit; first done.
    replace (uint.nat (word.add i 1)) with (S (uint.nat i)) by word.
    rewrite (take_S_r _ _ bkt); last first.
    { apply list_lookup_insert. word. }
    iApply (big_sepL_app).
    iSplitL "HbktsRP".
    { by rewrite take_insert; last auto. }
    iApply (big_sepL_singleton).
    rewrite take_length_le; last first.
    { rewrite insert_length. word. }
    replace (uint.nat i + 0)%nat with (uint.nat i); last word.
    rewrite /is_index_bucket.
    eauto 10 with iFrame.
  }
  { iSplitR "Hvchains"; last first.
    { iSplit; last done.
      iExactEq "Hvchains".
      f_equal.
      apply filter_all.
      word.
    }
    iExists (replicate (Z.to_nat N_IDX_BUCKET) null).
    auto with iFrame.
  }
  iIntros "[(HbktsInv & Hidx & _) HiRef]".
  iDestruct "HbktsInv" as (bktsL) "(HbktsS & %Hlength & HbktsRP)".
  unfold N_IDX_BUCKET in Hlength.
  wp_pures.

  (***********************************************************)
  (* return idx                                              *) 
  (***********************************************************)
  iApply "HΦ".
  rewrite /is_index.
  do 3 iExists _.
  iMod (readonly_alloc_1 with "Hidx") as "$".
  iMod (readonly_alloc_1 with "HbktsS") as "$".
  iModIntro.
  iSplitL ""; first done.
  iSplit; last iFrame "#".
  replace (uint.nat N_IDX_BUCKET) with (length bktsL); last first.
  { unfold N_IDX_BUCKET. word. }
  by rewrite firstn_all.
Qed.

End heap.
