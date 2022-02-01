(* Import definitions/theorems of the Perennial framework with the disk FFI. *)
From Perennial.program_proof Require Export disk_prelude.
(* Import Coq model of our Goose program. *)
From Goose.github_com.mit_pdos.go_mvcc Require Import txn.
From Perennial.program_proof.mvcc Require Import mvcc_ghost index_proof tuple_proof.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(**
 * 1. A txn is exposed to the client as two maps:
 *    a) `view`: one read-only map that represents the contents of the database on which
 *       the consistency predicate can be deduced,
 *    b) `mods`: another map that represents the updates made by the txn.
 * 2. `is_txn` connects the two maps with the following two kinds of resources:
 *    a) `view_ptsto k v` says that value `v` is stored at location `k`,
 *    b) `mods_token k` allows the txn to update `k`.
 * 3. These resources are defined by the underlying concurrency control protocol.
 *    They are granted on get and put, and returned on commit and abort.
 *    This roughly matches the idea of "reduction to two-phase locking".
 * 4. The spec of begin/commit/abort/get/put mentions only the two maps (`view` and `mods`),
 *    not the points-to facts (i.e., they are hidden behind `is_txn`).
 *    The client should be able to deduce the consistency predicate without expanding `is_txn`.
 * 5. The database invariant consists of:
 *    a) the authoritative element that represents the entire database,
 *    b) the consistency predicate,
 *    c) something that can give the client a proof that the txn actually executes.
 *)

(* Client-defined consistency predicate. *)
Definition C (m : gmap u64 u64) :=
  ∃ v0 v2,
    (m !! (U64 0) = Some v0) ∧ (m !! (U64 2) = Some v2) ∧
    (int.Z v0) + (int.Z v2) = 10.

(* `dbmap` is a map representing the entire database. *)
(*
Definition dbinv dbmap := ●dbmap ∗ (C dbmap) ∗ ●log.
 *)

Definition wrent_to_val (x : u64 * u64 * loc) :=
  (#x.1.1, (#x.1.2, (#x.2, #())))%V.

Definition own_txnmgr (txnmgr : loc) : iProp Σ := 
  ∃ (sidcur : u64) (sites : Slice.t)
    (* TODO: make `sites` a slice of pointers to `TxnSite` in the implementation. *)
    (sitesL : list loc),
    "Hsidcur" ∷ txnmgr ↦[TxnMgr :: "sidCur"] #sidcur ∗
    "Hsites" ∷ txnmgr ↦[TxnMgr :: "sites"] (to_val sites) ∗
    "HwsetL" ∷ slice.is_slice sites (structTy TxnSite) 1 (to_val <$> sitesL) ∗
    "_" ∷ True.

Definition is_txnmgr (txnmgr : loc) γ : iProp Σ := 
  ∃ (latch : loc) (sidcur : u64) (sites : Slice.t) (idx gc : loc)
    (sitesL : list loc),
    "#Hlatch" ∷ readonly (txnmgr ↦[TxnMgr :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (own_txnmgr txnmgr) ∗
    (* TODO: `is_idx` and `is_gc` *)
    "#Hidx" ∷ readonly (txnmgr ↦[TxnMgr :: "idx"] #idx) ∗
    "#HidxRI" ∷ is_index idx γ ∗
    "#Hgc" ∷ readonly (txnmgr ↦[TxnMgr :: "gc"] #gc) ∗
    "_" ∷ True.

Definition is_txn_impl (txn : loc) (view mods : gmap u64 u64) γ : iProp Σ :=
  ∃ (tid sid : u64) (wset : Slice.t) (idx txnmgr : loc)
    (wsetL : list (u64 * u64 * loc)),
    "Htid" ∷ txn ↦[Txn :: "tid"] #tid ∗
    "Hsid" ∷ txn ↦[Txn :: "sid"] #sid ∗
    "Hwset" ∷ txn ↦[Txn :: "wset"] (to_val wset) ∗
    "HwsetL" ∷ slice.is_slice wset (structTy WrEnt) 1 (wrent_to_val <$> wsetL) ∗
    "%HwsetLND" ∷ ⌜NoDup (fst <$> wsetL).*1⌝ (* keys are unique *) ∗
    "%Hmods_wsetL" ∷ ⌜mods = (list_to_map (fst <$> wsetL))⌝ ∗
    "#Hidx" ∷ readonly (txn ↦[Txn :: "idx"] #idx) ∗
    "#HidxRI" ∷ is_index idx γ ∗
    "Htxnmgr" ∷ txn ↦[Txn :: "txnMgr"] #txnmgr ∗
    "HtxnmgrRI" ∷ is_txnmgr txnmgr γ ∗
    "_" ∷ True.

Definition is_txn (txn : loc) (view mods : gmap u64 u64) γ : iProp Σ :=
  "%Hsubset" ∷ ⌜dom (gset u64) mods ⊆ dom (gset u64) view⌝ ∗
  (* TODO: separating permissions from values? *)
  "Hmods" ∷ ([∗ map] k ↦ _ ∈ mods, mods_token k) ∗
  "Hview" ∷ ([∗ map] k ↦ v ∈ view, view_ptsto k v) ∗
  "Himpl" ∷ is_txn_impl txn view mods γ.

Definition is_txn_uninit (txn : loc) γ : iProp Σ := 
  ∃ (tid sid : u64) (wset : Slice.t) (idx txnmgr : loc)
    (wsetL : list (u64 * u64 * loc)),
    "Htid" ∷ txn ↦[Txn :: "tid"] #tid ∗
    "Hsid" ∷ txn ↦[Txn :: "sid"] #sid ∗
    "Hwset" ∷ txn ↦[Txn :: "wset"] (to_val wset) ∗
    "HwsetL" ∷ slice.is_slice wset (structTy WrEnt) 1 (wrent_to_val <$> wsetL) ∗
    "#Hidx" ∷ readonly (txn ↦[Txn :: "idx"] #idx) ∗
    "#HidxRI" ∷ is_index idx γ ∗
    "Htxnmgr" ∷ txn ↦[Txn :: "txnMgr"] #txnmgr ∗
    "HtxnmgrRI" ∷ is_txnmgr txnmgr γ ∗
    "_" ∷ True.

Definition is_txnsite (txnsite : loc) : iProp Σ := 
  ∃ (latch : loc) (tidlast : u64) (tidsactive : Slice.t)
    (tidsactiveL : list u64),
    "#Hlatch" ∷ readonly (txnsite ↦[TxnSite :: "latch"] #latch) ∗
    "Htidlast" ∷ txnsite ↦[TxnSite :: "tidLast"] #tidlast ∗
    "Hwset" ∷ txnsite ↦[TxnSite :: "tidsActive"] (to_val tidsactive) ∗
    "HwsetL" ∷ typed_slice.is_slice tidsactive uint64T 1 tidsactiveL ∗
    "_" ∷ True.

Local Hint Extern 1 (environments.envs_entails _ (is_txn _ _ _ _)) => unfold is_txn : core.
Local Hint Extern 1 (environments.envs_entails _ (is_txn_impl _ _ _ _)) => unfold is_txn_impl : core.

(**
 * Extensions of a map are supersets of the map that we logically have
 * access to, but physically (i.e., the program) does not.
 *)

(* The client can use this theorem to deduce `C` without expanding the definition of `is_txn`. *)
Theorem db_consistent txn view mods γ :
  ⊢ is_txn txn view mods γ →
    ∃ dbmap, ⌜C dbmap ∧ view ⊆ dbmap⌝.
Proof.
  iIntros "Htxn".
  (* 1. Open `dbinv`. *)
  (* 2. Apply the agree rule to deduce that `view` is a subset of `dbmap`. *)
  (* 3. Deduce that `C` holds on `view`. *)
Admitted.

(*
{{{ True }}} wp_txn__New {{{ is_txn_uninit txn }}}
*)

(*****************************************************************)
(* func genTID(sid uint64) uint64                                *)
(*****************************************************************)
Theorem wp_genTID (sid : u64) :
  {{{ True }}}
    genTID #sid
  {{{ (tid : u64), RET #tid; True }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  wp_call.

  (***********************************************************)
  (* var tid uint64                                          *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first done.
  iIntros (tid) "Htid".
  wp_pures.
  wp_call.

  (***********************************************************)
  (* tid = tsc.GetTSC()                                      *)
  (***********************************************************)
  wp_apply wp_ArbitraryInt.
  iIntros (tsc) "_".

  (***********************************************************)
  (* tid = (tid & ^(config.N_TXN_SITES - 1)) + sid           *)
  (***********************************************************)
  wp_store.
  wp_load.
  wp_store.
  wp_load.

  (***********************************************************)
  (* return tid                                              *) 
  (***********************************************************)
  iApply "HΦ".
  done.
Qed.

Theorem wp_txnMgr__activate (txnmgr : loc) (sid : u64) γ :
  {{{ is_txnmgr txnmgr γ }}}
    TxnMgr__activate #txnmgr #sid
  {{{ (tid : u64), RET #tid; is_txnmgr txnmgr γ }}}.
Proof.
  iIntros (Φ) "Htxnmgr HΦ".
  iNamed "Htxnmgr".
  wp_call.
Admitted.

(*****************************************************************)
(* func (txn *Txn) Begin()                                       *)
(*****************************************************************)
Theorem wp_txn__Begin txn γ :
  {{{ is_txn_uninit txn γ }}}
    Txn__Begin #txn
  {{{ RET #(); is_txn txn ∅ ∅ γ }}}.
Proof.
  iIntros (Φ) "Htxn HΦ".
  iNamed "Htxn".
  wp_call.
  
  (***********************************************************)
  (* tid := txn.txnMgr.activate(txn.sid)                     *)
  (***********************************************************)
  wp_loadField.
  wp_loadField.
  wp_apply (wp_txnMgr__activate with "HtxnmgrRI").
  rename tid into tid_tmp.
  iIntros (tid) "HtxnmgrRI".

  (***********************************************************)
  (* txn.tid = tid                                           *)
  (***********************************************************)
  wp_pures.
  wp_storeField.
  
  (***********************************************************)
  (* txn.wset = txn.wset[:0]                                 *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_SliceTake); first word.
  wp_apply (wp_storeField with "Hwset"); first eauto.
  iIntros "Hwset".
  wp_pures.
  
  iApply "HΦ".
  iModIntro.
  rewrite /is_txn.
  do 3 (iSplitR; first eauto).
  iExists _, _, _, _, _, [].
  iFrame "# ∗".
  repeat rewrite fmap_nil.
  iDestruct (is_slice_take_cap _ _ _ (U64 0) with "HwsetL") as "H"; first word.
  iSplit; first done.
  iPureIntro.
  split; auto using NoDup_nil_2.
Qed.

(*****************************************************************)
(* func matchLocalWrites(key uint64, wset []WrEnt) (uint64, bool)*)
(*****************************************************************)
Local Lemma wp_matchLocalWrites (key : u64) (wset : Slice.t) (wsetL : list (u64 * u64 * loc)) :
  {{{ slice.is_slice wset (structTy WrEnt) 1 (wrent_to_val <$> wsetL) }}}
    matchLocalWrites #key (to_val wset)
  {{{ (pos : u64) (found : bool), RET (#pos, #found);
        slice.is_slice wset (structTy WrEnt) 1 (wrent_to_val <$> wsetL) ∗
        ⌜(found = false ∧ key ∉ wsetL.*1.*1) ∨
         (found = true ∧ ∃ went, wsetL !! (int.nat pos) = Some went ∧ went.1.1 = key)⌝
  }}}.
Proof.
  (***********************************************************)
  (* var idx uint64 = 0                                      *)
  (* var found bool = false                                  *)
  (* for {                                                   *)
  (*   if idx >= uint64(len(wset)) {                         *)
  (*     break                                               *)
  (*   }                                                     *)
  (*   if key == wset[idx].key {                             *)
  (*     found = true                                        *)
  (*     break                                               *)
  (*   }                                                     *)
  (*   idx++                                                 *)
  (* }                                                       *)
  (* return idx, found                                       *)
  (***********************************************************)
Admitted.

Definition get_spec txn view mods k v γ : iProp Σ :=
  match view !! k, mods !! k with
  (* `k` has not been read or written. *)
  | None, None => ∃ v', is_txn txn (<[k := v']> view) mods γ ∧ ⌜v = v'⌝
  (* `k` has been read, but not written. *)
  | Some vr, None => is_txn txn view mods γ ∧ ⌜v = vr⌝
  (* `k` has been written. *)
  | _, Some vw => is_txn txn view mods γ ∧ ⌜v = vw⌝
  end.

(*****************************************************************)
(* func (txn *Txn) Get(key uint64) (uint64, bool)                *)
(*****************************************************************)
Theorem wp_txn__Get txn (k : u64) (view mods : gmap u64 u64) γ :
  {{{ is_txn txn view mods γ }}}
    Txn__Get #txn #k
  {{{ (v : u64) (ok : bool), RET (#v, #ok); get_spec txn view mods k v γ }}}.
Proof.
  iIntros (Φ) "Htxn HΦ".
  iNamed "Htxn".
  iNamed "Himpl".
  wp_call.

  (***********************************************************)
  (* pos, found := matchLocalWrites(key, txn.wset)           *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_matchLocalWrites with "HwsetL").
  iIntros (pos found) "[HwsetL %Hmatch]".
  wp_pures.
  
  (***********************************************************)
  (* if found {                                              *)
  (*   val := txn.wset[pos].val                              *)
  (*   return val, true                                      *)
  (* }                                                       *)
  (***********************************************************)
  iDestruct (slice.is_slice_small_acc with "HwsetL") as "[HwsetL HwsetL_close]".
  wp_if_destruct.
  { wp_loadField.
    destruct Hmatch as [[contra _] | [_ [went [Hlookup Hkey]]]]; first congruence.
    wp_apply (wp_SliceGet with "[HwsetL]").
    { iFrame.
      iPureIntro.
      rewrite list_lookup_fmap.
      by rewrite Hlookup.
    }
    iIntros "[HwsetL %Hwent]".
    wp_pures.
    iApply "HΦ".
    iModIntro.
    rewrite /get_spec.
    (* Proving the third case of `get_spec` (write set hit). *)
    assert (HmodsSome : ∃ vm, mods !! k = Some vm).
    { exists went.1.2.
      rewrite Hmods_wsetL.
      rewrite -elem_of_list_to_map; last auto.
      apply elem_of_list_fmap_1_alt with went.
      { by apply elem_of_list_lookup_2 with (int.nat pos). }
      { rewrite -Hkey. auto using surjective_pairing. }
    }
    destruct HmodsSome as [vm HmodsSome].
    assert (HviewSome : ∃ vv, view !! k = Some vv).
    { apply elem_of_dom_2 in HmodsSome as Hinmods.
      (* Q: why doesn't the following work? *)
      (* destruct (elem_of_weaken _ _ _ Hinmods Hsubset). *)
      assert (Hinview : k ∈ dom (gset u64) view).
      { by apply elem_of_weaken with (dom (gset u64) mods). }
      by apply elem_of_dom in Hinview.
    }
    destruct HviewSome as [vv HviewSome].
    rewrite HviewSome.
    rewrite HmodsSome.
    iSplit; last first.
    { iPureIntro.
      rewrite Hmods_wsetL in HmodsSome.
      apply elem_of_list_lookup_2 in Hlookup.
      apply (elem_of_list_fmap_1 fst) in Hlookup.
      rewrite (surjective_pairing went.1) in Hlookup.
      rewrite Hkey in Hlookup.
      apply elem_of_list_to_map_1 in Hlookup; last auto.
      rewrite Hlookup in HmodsSome.
      by inversion HmodsSome.
    }
    iDestruct ("HwsetL_close" with "HwsetL") as "HwsetL".
    eauto 20 with iFrame.
  }

  (***********************************************************)
  (* idx := txn.idx                                          *)
  (* tuple := idx.GetTuple(key)                              *)
  (* valTuple, foundTuple := tuple.ReadVersion(txn.tid)      *)
  (* return valTuple, foundTuple                             *)
  (***********************************************************)
  iDestruct ("HwsetL_close" with "HwsetL") as "HwsetL".
  wp_loadField.
  wp_pures.
  wp_apply (wp_index__GetTuple with "HidxRI").
  iIntros (tuple) "#HtupleRI".
  wp_pures.
  wp_loadField.
  wp_apply (wp_tuple__ReadVersion with "HtupleRI").
  clear Heqb found.
  iIntros (val found) "Hview_ptsto'".
  wp_pures.
  iApply "HΦ".
  iModIntro.
  rewrite /get_spec.
  assert (HmodsNone : mods !! k = None).
  { destruct Hmatch as [[_ Hnotin] | [contra _]]; last congruence.
    rewrite Hmods_wsetL.
    by apply not_elem_of_list_to_map.
  }
  rewrite HmodsNone.
  destruct (view !! k) eqn:Eqlookup.
  { (* Proving the second case of `get_spec` (write set misses / non-first read). *)
    iDestruct (big_sepM_lookup_acc _ view k u with "[Hview]") as "[Hview_ptsto Hview_close]"; [auto | auto |].
    iDestruct (view_ptsto_agree with "Hview_ptsto Hview_ptsto'") as %->.
    iDestruct ("Hview_close" with "Hview_ptsto") as "Hview".
    iSplit; last done.
    eauto 20 with iFrame.
  }
  { (* Proving the first case of `get_spec` (write set misses / first read). *)
    iExists val.
    iSplit; last done.
    rewrite /is_txn.
    iSplit.
    { iPureIntro.
      rewrite dom_insert.
      set_solver.
    }
    iFrame "Hmods".
    iSplitL "Hview Hview_ptsto'".
    { iApply big_sepM_insert; done. }
    eauto 20 with iFrame.
  }
  (* Qed. *)
  (* Error: The following section variable is used but not declared: mvcc_ghostG0 *)
Admitted.

Definition put_spec txn view mods k v γ : iProp Σ :=
  match view !! k, mods !! k with
  (* `k` has not been read or written; note that `v'` is not tied to any program variable. *)
  | None, None => ∃ v', is_txn txn (<[k := v']> view) (<[k := v]> mods) γ
  (* `k` has been read or written. *)
  | _, _ => is_txn txn view (<[k := v]> mods) γ
  end.

Theorem wp_txn__Put txn (k : u64) (v : u64) (view mods : gmap u64 u64) γ :
  {{{ is_txn txn view mods γ }}}
    Txn__Put #txn #k #v
  {{{ (ok : bool), RET #ok; put_spec txn view mods k v γ }}}.
Proof.
  iIntros (Φ) "Htxn HΦ".
  iNamed "Htxn".
  iNamed "Himpl".
  wp_call.
Admitted.

(* The client is responsible for proving C holds on all the updated extensions of `view`. *)
Theorem wp_txn__Commit txn view mods γ :
  {{{ ∀ dbmap, ⌜view ⊆ dbmap → C dbmap → C (mods ∪ dbmap)⌝ ∗ is_txn txn view mods γ }}}
    Txn__Commit #txn
  {{{ RET #(); is_txn_uninit txn γ (* * sth about log *) }}}.
Admitted.

End heap.
