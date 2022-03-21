(* Import definitions/theorems of the Perennial framework with the disk FFI. *)
From Perennial.program_proof Require Export disk_prelude.
(* Import Coq model of our Goose program. *)
From Goose.github_com.mit_pdos.go_mvcc Require Import txn.
From Perennial.program_proof.mvcc Require Import mvcc_ghost gc_proof index_proof tuple_proof.

Section lemmas.
Context `{FinMap K M}.

Lemma list_delete_insert_delete {A} (l : list A) i v :
  (i < length l)%nat ->
  delete i (<[i := v]> l) = delete i l.
Proof.
  intros.
  rewrite insert_take_drop; last done.
  rewrite delete_take_drop.
  replace i with (length (take i l)) at 1; last first.
  { apply take_length_le. lia. }
  rewrite take_app.
  rewrite cons_middle.
  replace (S i) with (length (take i l ++ [v])); last first.
  { rewrite app_length.
    simpl.
    rewrite take_length_le; last lia.
    lia.
  }
  rewrite app_assoc.
  rewrite drop_app.
  rewrite app_length.
  simpl.
  rewrite take_length_le; last lia.
  replace (i + 1)%nat with (S i)%nat by lia.
  by rewrite -delete_take_drop.
Qed.
  
Lemma list_to_map_insert {A} (l : list (K * A)) k v v' i :
  NoDup l.*1 ->
  l !! i = Some (k, v) ->
  <[k := v']> (list_to_map l) =@{M A} list_to_map (<[i := (k, v')]> l).
Proof using EqDecision0 H H0 H1 H2 H3 H4 H5 H6 K M.
  (* FIXME... *)
  intros.
  apply lookup_lt_Some in H8 as Hlength.
  apply delete_Permutation in H8 as Hperm.
  apply Permutation_sym in Hperm.
  rewrite -(list_to_map_proper ((k, v) :: (delete i l)) l); last done; last first.
  { apply NoDup_Permutation_proper with l.*1; [by apply fmap_Permutation | done]. }
  set l' := <[_:=_]> l.
  assert (Hlookup : l' !! i = Some (k, v')).
  { rewrite list_lookup_insert; auto. }
  apply delete_Permutation in Hlookup as Hperm'.
  apply Permutation_sym in Hperm'.
  rewrite -(list_to_map_proper ((k, v') :: (delete i l')) l'); last done; last first.
  { apply NoDup_Permutation_proper with l'.*1; first by apply fmap_Permutation.
    rewrite list_fmap_insert.
    simpl.
    rewrite list_insert_id; first done.
    rewrite list_lookup_fmap.
    by rewrite H8.
  }
  do 2 rewrite list_to_map_cons.
  rewrite insert_insert.
  by rewrite list_delete_insert_delete.
Qed.

End lemmas.

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
Definition C (m : gmap u64 dbval) :=
  ∃ v0 v2,
    (m !! (U64 0) = Some (Value v0)) ∧ (m !! (U64 2) = Some (Value v2)) ∧
    (int.Z v0) + (int.Z v2) = 10.

(* `dbmap` is a map representing the entire database. *)
(*
Definition dbinv dbmap := ●dbmap ∗ (C dbmap) ∗ ●log.
 *)

Definition wrent := (u64 * (bool * u64) * loc)%type.

Definition wrent_to_val (x : wrent) :=
  (#x.1.1, (#x.1.2.1, (#x.1.2.2, #()), (#x.2, #())))%V.

Definition N_TXN_SITES : Z := 64.

Definition own_txnsite (txnsite : loc) : iProp Σ := 
  ∃ (tidlast : u64) (tidsactive : Slice.t)
    (tidsactiveL : list u64),
    "Htidlast" ∷ txnsite ↦[TxnSite :: "tidLast"] #tidlast ∗
    "Hactive" ∷ txnsite ↦[TxnSite :: "tidsActive"] (to_val tidsactive) ∗
    "HactiveL" ∷ typed_slice.is_slice tidsactive uint64T 1 tidsactiveL ∗
    "_" ∷ True.
Local Hint Extern 1 (environments.envs_entails _ (own_txnsite _)) => unfold own_txnsite : core.

Definition is_txnsite (site : loc) : iProp Σ := 
  ∃ (latch : loc),
    "#Hlatch" ∷ readonly (site ↦[TxnSite :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (own_txnsite site) ∗
    "_" ∷ True.

Definition own_txnmgr (txnmgr : loc) : iProp Σ := 
  ∃ (sidcur : u64),
    "Hsidcur" ∷ txnmgr ↦[TxnMgr :: "sidCur"] #sidcur ∗
    "%HsidcurB" ∷ ⌜(int.Z sidcur) < N_TXN_SITES⌝ ∗
    "_" ∷ True.
Local Hint Extern 1 (environments.envs_entails _ (own_txnmgr _)) => unfold own_txnmgr : core.

Definition is_txnmgr (txnmgr : loc) γ : iProp Σ := 
  ∃ (latch : loc) (sites : Slice.t) (idx gc : loc)
    (sitesL : list loc),
    "#Hlatch" ∷ readonly (txnmgr ↦[TxnMgr :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (own_txnmgr txnmgr) ∗
    "#Hidx" ∷ readonly (txnmgr ↦[TxnMgr :: "idx"] #idx) ∗
    "#HidxRI" ∷ is_index idx γ ∗
    "#Hgc" ∷ readonly (txnmgr ↦[TxnMgr :: "gc"] #gc) ∗
    "#Hsites" ∷ readonly (txnmgr ↦[TxnMgr :: "sites"] (to_val sites)) ∗
    "#HsitesS" ∷ readonly (is_slice_small sites ptrT 1 (to_val <$> sitesL)) ∗
    "%HsitesLen" ∷ ⌜Z.of_nat (length sitesL) = N_TXN_SITES⌝ ∗
    "#HsitesRP" ∷ ([∗ list] _ ↦ site ∈ sitesL, is_txnsite site) ∗
    "_" ∷ True.
Local Hint Extern 1 (environments.envs_entails _ (is_txnmgr _ _)) => unfold is_txnmgr : core.

Local Definition to_dbval (x : bool * u64) :=
  if x.1 then Nil else Value x.2.

Local Definition wrent_to_key_dbval (ent : wrent) : (u64 * dbval) :=
  ((prod_map id to_dbval) ∘ fst) ent.

Definition is_txn_impl (txn : loc) (tid : u64) (view mods : gmap u64 dbval) γ : iProp Σ :=
  ∃ (sid : u64) (wset : Slice.t) (idx txnmgr : loc)
    (wsetL : list wrent),
    "Htid" ∷ txn ↦[Txn :: "tid"] #tid ∗
    "Hsid" ∷ txn ↦[Txn :: "sid"] #sid ∗
    "%HsidB" ∷ ⌜(int.Z sid) < N_TXN_SITES⌝ ∗
    "Hwset" ∷ txn ↦[Txn :: "wset"] (to_val wset) ∗
    "HwsetL" ∷ slice.is_slice wset (structTy WrEnt) 1 (wrent_to_val <$> wsetL) ∗
    "%HwsetLND" ∷ ⌜NoDup (fst <$> wsetL).*1⌝ (* keys are unique *) ∗
    "%Hmods_wsetL" ∷ ⌜mods = (list_to_map (wrent_to_key_dbval <$> wsetL))⌝ ∗
    "#Hidx" ∷ readonly (txn ↦[Txn :: "idx"] #idx) ∗
    "#HidxRI" ∷ is_index idx γ ∗
    "#Htxnmgr" ∷ readonly (txn ↦[Txn :: "txnMgr"] #txnmgr) ∗
    "#HtxnmgrRI" ∷ is_txnmgr txnmgr γ ∗
    "Hactive" ∷ active_tid γ tid ∗
    "_" ∷ True.
Local Hint Extern 1 (environments.envs_entails _ (is_txn_impl _ _ _ _ _)) => unfold is_txn_impl : core.

Definition is_txn (txn : loc) (view mods : gmap u64 dbval) γ : iProp Σ :=
  ∃ (tid : u64),
    "Hmods" ∷ ([∗ map] k ↦ _ ∈ mods, mods_token γ k tid) ∗
    "Hview" ∷ ([∗ map] k ↦ v ∈ view, view_ptsto γ k v tid) ∗
    "Himpl" ∷ is_txn_impl txn tid view mods γ.
Local Hint Extern 1 (environments.envs_entails _ (is_txn _ _ _ _)) => unfold is_txn : core.

Definition is_txn_uninit (txn : loc) γ : iProp Σ := 
  ∃ (tid sid : u64) (wset : Slice.t) (idx txnmgr : loc)
    (wsetL : list wrent),
    "Htid" ∷ txn ↦[Txn :: "tid"] #tid ∗
    "Hsid" ∷ txn ↦[Txn :: "sid"] #sid ∗
    "%HsidB" ∷ ⌜(int.Z sid) < N_TXN_SITES⌝ ∗
    "Hwset" ∷ txn ↦[Txn :: "wset"] (to_val wset) ∗
    "HwsetL" ∷ slice.is_slice wset (structTy WrEnt) 1 (wrent_to_val <$> wsetL) ∗
    "#Hidx" ∷ readonly (txn ↦[Txn :: "idx"] #idx) ∗
    "#HidxRI" ∷ is_index idx γ ∗
    "#Htxnmgr" ∷ readonly (txn ↦[Txn :: "txnMgr"] #txnmgr) ∗
    "#HtxnmgrRI" ∷ is_txnmgr txnmgr γ ∗
    "_" ∷ True.

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

(*****************************************************************)
(* func MkTxnMgr() *TxnMgr                                       *)
(*****************************************************************)
Theorem wp_MkTxnMgr γ :
  {{{ True }}}
    MkTxnMgr #()
  {{{ (txnmgr : loc), RET #txnmgr; is_txnmgr txnmgr γ }}}.
Proof using mvcc_ghostG0.
  iIntros (Φ) "_ HΦ".
  wp_call.

  (***********************************************************)
  (* txnMgr := new(TxnMgr)                                   *)
  (* txnMgr.latch = new(sync.Mutex)                          *)
  (* txnMgr.sites = make([]*TxnSite, config.N_TXN_SITES)     *)
  (***********************************************************)
  wp_apply (wp_allocStruct); first auto 10.
  iIntros (txnmgr) "Htxnmgr".
  iDestruct (struct_fields_split with "Htxnmgr") as "Htxnmgr".
  iNamed "Htxnmgr".
  simpl.
  wp_pures.
  wp_apply (wp_new_free_lock).
  iIntros (latch) "Hfree".
  wp_storeField.
  wp_apply (wp_new_slice); first done.
  iIntros (sites) "HsitesL".
  wp_storeField.
  
  (***********************************************************)
  (* for i := uint64(0); i < config.N_TXN_SITES; i++ {       *)
  (*     site := new(TxnSite)                                *)
  (*     site.latch = new(sync.Mutex)                        *)
  (*     site.tidsActive = make([]uint64, 0, 8)              *)
  (*     txnMgr.sites[i] = site                              *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_ref_to); first auto.
  iIntros (iRef) "HiRef".
  wp_pures.
  iDestruct (is_slice_to_small with "HsitesL") as "HsitesS".
  wp_apply (wp_forUpto
              (λ n, (∃ sitesL, (is_slice_small sites ptrT 1 (to_val <$> sitesL)) ∗
                               (⌜Z.of_nat (length sitesL) = N_TXN_SITES⌝) ∗
                               ([∗ list] site ∈ (take (int.nat n) sitesL), is_txnsite site)) ∗
                    (txnmgr ↦[TxnMgr :: "sites"] (to_val sites)) ∗
                    ⌜True⌝)%I
              _ _ (U64 0) (U64 N_TXN_SITES) with "[] [HsitesS $sites $HiRef]"); first done.
  { clear Φ latch.
    iIntros (i Φ) "!> ((HsitesInv & Htxnmgr & _) & HiRef & %Hbound) HΦ".
    iDestruct "HsitesInv" as (sitesL) "(HsitesS & %Hlength & HsitesRP)".
    wp_pures.
    wp_apply (wp_allocStruct); first auto 10.
    iIntros (site) "Hsite".
    iDestruct (struct_fields_split with "Hsite") as "Hsite".
    iNamed "Hsite".
    simpl.
    wp_pures.
    wp_apply (wp_new_free_lock).
    iIntros (latch) "Hfree".
    wp_storeField.
    wp_apply (wp_NewSlice (V:=u64)).
    iIntros (active) "HactiveL".
    wp_storeField.
    wp_load.
    wp_loadField.
    replace (int.Z 64) with (Z.of_nat (length sitesL)) in Hbound.
    unfold N_TXN_SITES in *.
    wp_apply (wp_SliceSet with "[$HsitesS]").
    { iPureIntro.
      split; last auto.
      apply lookup_lt_is_Some.
      rewrite fmap_length.
      word.
    }
    iIntros "HsitesS".
    wp_pures.
    iApply "HΦ".
    iFrame.
    
    iMod (readonly_alloc_1 with "latch") as "#Hlatch".
    iMod (alloc_lock mvccN _ latch (own_txnsite site) with "[$Hfree] [-HsitesS HsitesRP]") as "#Hlock".
    { eauto 10 with iFrame. }
    iModIntro.
    rewrite -list_fmap_insert.
    iExists _.
    iFrame.
    rewrite insert_length.
    iSplit; first done.
    replace (int.nat (word.add i 1)) with (S (int.nat i)); last word.
    rewrite (take_S_r _ _ site); last first.
    { apply list_lookup_insert. word. }
    iApply (big_sepL_app).
    iSplitL "HsitesRP".
    { by rewrite take_insert; last auto. }
    iApply (big_sepL_singleton).
    rewrite /is_txnsite.
    eauto 10 with iFrame.
  }
  { iExists (replicate 64 null).
    auto with iFrame.
  }
  iIntros "[(HsitesInv & Hsites & _) HiRef]".
  iDestruct "HsitesInv" as (sitesL) "(HsitesS & %Hlength & #HsitesRP)".
  wp_pures.

  (***********************************************************)
  (* txnMgr.idx = index.MkIndex()                            *)
  (* txnMgr.gc = gc.MkGC(txnMgr.idx)                         *)
  (***********************************************************)
  wp_apply (wp_MkIndex γ).
  iIntros (idx) "#HidxRP".
  wp_storeField.
  wp_loadField.
  wp_apply (wp_MkGC _ γ).
  (* iIntros (gc) "HgcRP". *)
  iIntros (gc) "_".
  wp_storeField.
  
  (***********************************************************)
  (* return txnMgr                                           *)
  (***********************************************************)
  iApply "HΦ".
  rewrite /is_txnmgr.
  iMod (readonly_alloc_1 with "latch") as "#Hlatch".
  iMod (alloc_lock mvccN _ latch (own_txnmgr txnmgr) with "[$Hfree] [sidCur]") as "#Hlock".
  { eauto with iFrame. }
  iMod (readonly_alloc_1 with "idx") as "#Hidx".
  iMod (readonly_alloc_1 with "gc") as "#Hgc".
  iMod (readonly_alloc_1 with "Hsites") as "#Hsites".
  iMod (readonly_alloc_1 with "HsitesS") as "#HsitesS".
  replace (int.nat (U64 N_TXN_SITES)) with (length sitesL); last first.
  { unfold N_TXN_SITES in *. word. }
  rewrite firstn_all.
  eauto 20 with iFrame.
Qed.

(*****************************************************************)
(* func (txnMgr *TxnMgr) New() *Txn                              *)
(*****************************************************************)
Theorem wp_txnMgr__New txnmgr γ :
  is_txnmgr txnmgr γ -∗
  {{{ True }}}
    TxnMgr__New #txnmgr
  {{{ (txn : loc), RET #txn; is_txn_uninit txn γ }}}.
Proof.
  iIntros "#Htxnmgr" (Φ) "!> _ HΦ".
  iNamed "Htxnmgr".
  wp_call.
  
  (***********************************************************)
  (* txnMgr.latch.Lock()                                     *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HtxnmgrOwn]".
  iNamed "HtxnmgrOwn".
  wp_pures.
  
  (***********************************************************)
  (* txn := new(Txn)                                         *)
  (* txn.wset = make([]WrEnt, 0, 32)                         *)
  (***********************************************************)
  wp_apply (wp_allocStruct); first auto 10.
  iIntros (txn) "Htxn".
  iDestruct (struct_fields_split with "Htxn") as "Htxn".
  iNamed "Htxn".
  simpl.
  wp_pures.
  wp_apply (wp_new_slice); first done.
  iIntros (wset) "HwsetL".
  wp_storeField.
          
  (***********************************************************)
  (* sid := txnMgr.sidCur                                    *)
  (* txn.sid = sid                                           *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_storeField.
  
  (***********************************************************)
  (* txn.idx = txnMgr.idx                                    *)
  (* txn.txnMgr = txnMgr                                     *)
  (***********************************************************)
  wp_loadField.
  do 2 wp_storeField.
  
  (***********************************************************)
  (* txnMgr.sidCur = sid + 1                                 *)
  (* if txnMgr.sidCur == config.N_TXN_SITES {                *)
  (*     txnMgr.sidCur = 0                                   *)
  (* }                                                       *)
  (***********************************************************)
  wp_storeField.
  wp_loadField.
  wp_apply (wp_If_join_evar with "[Hsidcur]").
  { iIntros (b') "%Eb'".
    case_bool_decide.
    { wp_if_true.
      wp_storeField.
      iSplit; first done.
      replace (U64 0) with (if b' then (U64 0) else (word.add sidcur (U64 1))) by by rewrite Eb'.
      iNamedAccu.
    }
    { wp_if_false.
      iModIntro.
      subst.
      by iFrame "∗".
    }
  }
  iIntros "H".
  iNamed "H".
  wp_pures.
    
  (***********************************************************)
  (* txnMgr.latch.Unlock()                                   *)
  (* return txn                                              *)
  (***********************************************************)
  wp_loadField.
  wp_apply (release_spec with "[Hlocked Hsidcur]").
  { iFrame "Hlock Hlocked".
    iNext.
    unfold own_txnmgr.
    iExists _.
    iFrame.
    iSplit; last done.
    iPureIntro.
    case_bool_decide; first done.
    unfold N_TXN_SITES in *.
    apply Znot_le_gt in H.
    by apply Z.gt_lt.
  }
  wp_pures.
  iApply "HΦ".
  iMod (readonly_alloc_1 with "idx") as "#Hidx_txn".
  iMod (readonly_alloc_1 with "txnMgr") as "#Htxnmgr_txn".
  replace (int.nat 0) with 0%nat by word.
  simpl.
  unfold is_txn_uninit.
  do 5 iExists _.
  iExists [].
  iFrame "# ∗".
  eauto 20 with iFrame.
Qed.

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

(*****************************************************************)
(* func (txnMgr *TxnMgr) activate(sid uint64) uint64             *)
(*****************************************************************)
Theorem wp_txnMgr__activate (txnmgr : loc) (sid : u64) γ :
  is_txnmgr txnmgr γ -∗
  {{{ ⌜(int.Z sid) < N_TXN_SITES⌝ }}}
    TxnMgr__activate #txnmgr #sid
  {{{ (tid : u64), RET #tid; active_tid γ tid }}}.
Proof.
  iIntros "#Htxnmgr !>" (Φ) "%HsitesBound HΦ".
  iNamed "Htxnmgr".
  wp_call.
  
  (***********************************************************)
  (* site := txnMgr.sites[sid]                               *)
  (* site.latch.Lock()                                       *)
  (***********************************************************)
  wp_loadField.
  iMod (readonly_load with "HsitesS") as (q) "HsitesS'".
  list_elem sitesL (int.nat sid) as site.
  wp_apply (wp_SliceGet with "[$HsitesS']").
  { iPureIntro.
    rewrite list_lookup_fmap.
    by rewrite Hsite_lookup.
  }
  iIntros "HsitesS'".
  wp_pures.

  iDestruct (big_sepL_lookup with "HsitesRP") as "HsiteRP"; first done.
  iClear (latch) "Hlatch Hlock".
  iNamed "HsiteRP".
  wp_loadField.
  wp_apply (acquire_spec with "[$Hlock]").
  iIntros "[Hlocked HsiteOwn]".
  iNamed "HsiteOwn".
  wp_pures.
  
  (***********************************************************)
  (* var tid uint64                                          *)
  (* tid = genTID(sid)                                       *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first done.
  iIntros (tidRef) "HtidRef".
  wp_pures.
  wp_apply (wp_genTID).
  iIntros (tid) "_".
  wp_store.
  wp_pures.
  
  (***********************************************************)
  (* for tid <= site.tidLast {                               *)
  (*     tid = genTID(sid)                                   *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool), (∃ (tidLoop : u64),
             "Htidlast" ∷ site ↦[TxnSite :: "tidLast"] #tidlast ∗
             "HtidRef" ∷ tidRef ↦[uint64T] #tidLoop ∗
             "%Hexit" ∷ if b then ⌜True⌝ else ⌜(int.Z tidLoop) > (int.Z tidlast)⌝)%I.
  wp_apply (wp_forBreak_cond P with "[] [Htidlast HtidRef]").
  { clear Φ.
    iIntros (Φ) "!> Hloop HΦ".
    iNamed "Hloop".
    wp_load.
    wp_loadField.
    wp_pures.
    case_bool_decide.
    - wp_if_true.
      wp_pures.
      wp_apply (wp_genTID).
      iIntros (tid'') "_".
      wp_store.
      iApply "HΦ".
      unfold P.
      eauto with iFrame.
    - wp_if_false.
      iApply "HΦ".
      unfold P.
      apply Znot_le_gt in H.
      eauto with iFrame.
  }
  { unfold P. eauto with iFrame. }
  iIntros "Hloop".
  iNamed "Hloop".
  wp_pures.
  
  (***********************************************************)
  (* site.tidLast = tid                                      *)
  (* site.tidsActive = append(site.tidsActive, tid)          *)
  (* site.latch.Unlock()                                     *)
  (* return tid                                              *)
  (***********************************************************)
  wp_load.
  wp_storeField.
  wp_load.
  wp_loadField.
  wp_apply (typed_slice.wp_SliceAppend (V := u64) with "HactiveL").
  iIntros (tidsactive') "HactiveL".
  wp_storeField.
  wp_loadField.
  wp_apply (release_spec with "[-HΦ HtidRef]").
  { eauto 10 with iFrame. }
  wp_pures.
  wp_load.
  iApply "HΦ".
  admit.
  (* TODO: prove [active_tid γ tid]. *)
Admitted.

(*****************************************************************)
(* func (txnMgr *TxnMgr) getMinActiveTID() uint64                *)
(*****************************************************************)
Theorem wp_txnMgr__getMinActiveTID txnmgr γ :
  {{{ True }}}
    TxnMgr__getMinActiveTID txnmgr
  {{{ (tid : u64), RET #tid; min_tid_lb γ (int.nat tid) }}}.
Proof.
  (***********************************************************)
  (* var min uint64 = config.TID_SENTINEL                    *)
  (* for sid := uint64(0); sid < config.N_TXN_SITES; sid++ { *)
  (*     tid := txnMgr.getMinActiveTIDSite(sid)              *)
  (*     if tid < min {                                      *)
  (*         min = tid                                       *)
  (*     }                                                   *)
  (* }                                                       *)
  (* return min                                              *)
  (***********************************************************)
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
  wp_apply (wp_txnMgr__activate with "HtxnmgrRI"); first done.
  rename tid into tid_tmp.
  iIntros (tid) "Hactive".

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
  iExists tid.
  do 2 (iSplitR; first eauto).
  iExists _, _, _, _, [].
  iFrame "# ∗".
  repeat rewrite fmap_nil.
  iDestruct (is_slice_take_cap _ _ _ (U64 0) with "HwsetL") as "H"; first word.
  iSplit; first done.
  iSplit; first done.
  iPureIntro.
  split; auto using NoDup_nil_2.
Qed.

Local Lemma val_to_wrent_with_val_ty (x : val) :
  val_ty x (uint64T * (boolT * (uint64T * unitT) * (ptrT * unitT))%ht) ->
  (∃ (k : u64) (d : bool) (v : u64) (t : loc), x = wrent_to_val (k, (d, v), t)).
Proof.
  intros H.
  inversion_clear H. 
  { inversion H0. }
  inversion_clear H0.
  inversion_clear H.
  inversion_clear H1.
  { inversion H. }
  inversion_clear H.
  { inversion H1. }
  inversion_clear H1.
  inversion_clear H.
  inversion_clear H2.
  { inversion H. }
  inversion_clear H.
  inversion_clear H2.
  inversion_clear H0.
  { inversion H. }
  inversion_clear H.
  inversion_clear H0.
  inversion_clear H1.
  inversion_clear H.
  inversion_clear H2.
  inversion_clear H.
  exists x0, x1, x2, x3.
  reflexivity.
Qed.

(*****************************************************************)
(* func matchLocalWrites(key uint64, wset []WrEnt) (uint64, bool)*)
(*****************************************************************)
Local Lemma wp_matchLocalWrites (key : u64) (wset : Slice.t) (wsetL : list wrent) :
  {{{ slice.is_slice wset (structTy WrEnt) 1 (wrent_to_val <$> wsetL) }}}
    matchLocalWrites #key (to_val wset)
  {{{ (pos : u64) (found : bool), RET (#pos, #found);
        slice.is_slice wset (structTy WrEnt) 1 (wrent_to_val <$> wsetL) ∗
        ⌜(found = false ∧ key ∉ wsetL.*1.*1) ∨
         (found = true ∧ ∃ went, wsetL !! (int.nat pos) = Some went ∧ went.1.1 = key)⌝
  }}}.
Proof.
  iIntros (Φ) "HwsetL HΦ".
  wp_call.
  
  (***********************************************************)
  (* var pos uint64 = 0                                      *)
  (***********************************************************)
  wp_apply (wp_ref_to); first auto.
  iIntros (posR) "HposR".
  wp_pures.
  
  (***********************************************************)
  (* for {                                                   *)
  (*     if pos >= uint64(len(wset)) {                       *)
  (*         break                                           *)
  (*     }                                                   *)
  (*     if key == wset[pos].key {                           *)
  (*         break                                           *)
  (*     }                                                   *)
  (*     pos++                                               *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_forBreak
              (λ b,
                 (slice.is_slice wset (struct.t WrEnt) 1 (wrent_to_val <$> wsetL)) ∗
                 (∃ (pos : u64),
                    posR ↦[uint64T] #pos ∗
                    (⌜(int.Z pos) ≤ (int.Z wset.(Slice.sz))⌝) ∗
                    (⌜if b then True
                      else (∃ (ent : wrent), wsetL !! (int.nat pos) = Some ent ∧ ent.1.1 = key) ∨
                           (int.Z wset.(Slice.sz)) ≤ (int.Z pos)⌝) ∗
                    (⌜key ∉ (take (int.nat pos) wsetL.*1.*1)⌝)))%I
              with "[] [$HwsetL HposR]").
  { clear Φ.
    iIntros (Φ).
    iModIntro.
    iIntros "[HwsetL Hinv] HΦ".
    iDestruct "Hinv" as (pos) "(Hpos & %Hbound & _ & %Hnotin)".
    wp_pures.
    wp_apply (wp_slice_len).
    wp_load.
    wp_if_destruct.
    { iApply "HΦ".
      eauto 10 with iFrame.
    }
    wp_load.
    iDestruct (slice.is_slice_small_acc with "HwsetL") as "[HwsetS HwsetL]".
    iDestruct (slice.is_slice_small_sz with "[$HwsetS]") as "%HwsetSz".
    destruct (list_lookup_lt _ (wrent_to_val <$> wsetL) (int.nat pos)) as [ent HSome].
    { apply Z.nle_gt in Heqb.
      word.
    }
    wp_apply (slice.wp_SliceGet with "[HwsetS]"); first auto.
    iIntros "[HwsetS %HwsetT]".
    iDestruct ("HwsetL" with "HwsetS") as "HwsetL".
    destruct (val_to_wrent_with_val_ty _ HwsetT) as (k & d & v & t & H).
    subst.
    wp_pures.
    wp_if_destruct.
    { iApply "HΦ".
      iModIntro.
      iFrame.
      iExists pos.
      iFrame.
      iPureIntro.
      split; first done.
      split; last done.
      left.
      exists (k, (d, v), t).
      split; last done.
      rewrite list_lookup_fmap in HSome.
      apply fmap_Some in HSome as [ent [HSome H]].
      rewrite HSome.
      f_equal.
      inversion H.
      rewrite -(surjective_pairing ent.1.2).
      rewrite -(surjective_pairing ent.1).
      rewrite -(surjective_pairing ent).
      done.
    }
    wp_load.
    wp_pures.
    wp_store.
    iModIntro.
    iApply "HΦ".
    iFrame.
    iExists (word.add pos 1%Z).
    iFrame.
    iPureIntro.
    split; first word.
    split; first done.
    replace (int.nat (word.add pos 1)) with (S (int.nat pos)); last word.
    apply Z.nle_gt in Heqb.
    rewrite (take_S_r _ _ k); last first.
    { rewrite list_lookup_fmap in HSome.
      apply fmap_Some in HSome as [ent [HSome H]].
      inversion H.
      do 2 rewrite list_lookup_fmap.
      rewrite HSome.
      done.
    }
    apply not_elem_of_app.
    split; first done.
    simpl.
    rewrite elem_of_list_singleton.
    unfold not.
    intros Eqkey.
    rewrite Eqkey in Heqb0.
    contradiction.
  }
  { iExists (U64 0).
    iFrame.
    iPureIntro.
    change (int.nat 0) with 0%nat.
    rewrite take_0.
    split; first word.
    split; auto using not_elem_of_nil.
  }
  iIntros "[HwsetL Hinv]".
  iDestruct "Hinv" as (pos) "(Hpos & _ & %Hexit & %Hnotin)".
  wp_pures.
  
  (***********************************************************)
  (* found := pos < uint64(len(wset))                        *)
  (* return pos, found                                       *)
  (***********************************************************)
  wp_load.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_load.
  iDestruct (is_slice_sz with "HwsetL") as "%Hsz".
  rewrite fmap_length in Hsz.
  case_bool_decide; (wp_pures; iModIntro; iApply "HΦ"; iFrame; iPureIntro).
  { (* Write entry found. *)
    right.
    split; first done.
    destruct Hexit; [done | word].
  }
  { (* Write entry not found. *)
    left.
    split; first done.
    apply Z.nlt_ge in H.
    rewrite take_ge in Hnotin; first done.
    do 2 rewrite fmap_length.
    rewrite Hsz.
    word.
  }
Qed.

Definition spec_get txn view mods k v γ : iProp Σ :=
  match mods !! k, view !! k with
  (* `k` has not been read or written. *)
  | None, None => ∃ v', is_txn txn (<[k := v']> view) mods γ ∧ ⌜v = v'⌝
  (* `k` has been read, but not written. *)
  | None, Some vr => is_txn txn view mods γ ∧ ⌜v = vr⌝
  (* `k` has been written. *)
  | Some vw, _ => is_txn txn view mods γ ∧ ⌜v = vw⌝
  end.

Local Lemma NoDup_wrent_to_key_dbval (wset : list wrent) :
  NoDup wset.*1.*1 ->
  NoDup (wrent_to_key_dbval <$> wset).*1.
Proof.
  intros H.
  replace (wrent_to_key_dbval <$> _).*1 with wset.*1.*1; last first.
  { do 2 rewrite -list_fmap_compose.
    f_equal.
  }
  done.
Qed.

Local Lemma wrent_to_key_dbval_key_fmap (ents : list wrent) :
  (wrent_to_key_dbval <$> ents).*1 = ents.*1.*1.
Proof.
  do 2 rewrite -list_fmap_compose.
  by apply list_fmap_ext; last done.
Qed.

(*****************************************************************)
(* func (txn *Txn) Get(key uint64) (uint64, bool)                *)
(*****************************************************************)
Theorem wp_txn__Get txn (k : u64) (view mods : gmap u64 dbval) γ :
  {{{ is_txn txn view mods γ }}}
    Txn__Get #txn #k
  {{{ (v : u64) (found : bool), RET (#v, #found); spec_get txn view mods k (if found then Value v else Nil) γ }}}.
Proof using mvcc_ghostG0.
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
  (*     dbval := txn.wset[pos].val                          *)
  (*     return dbval.val, !dbval.tomb                       *)
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
    rewrite /spec_get.
    (* Proving the third case of `spec_get` (write set hit). *)
    assert (HmodsSome : ∃ vm, mods !! k = Some vm).
    { exists (if went.1.2.1 then Nil else Value went.1.2.2).
      rewrite Hmods_wsetL.
      rewrite -elem_of_list_to_map; last by apply NoDup_wrent_to_key_dbval.
      apply elem_of_list_fmap_1_alt with went.
      { by apply elem_of_list_lookup_2 with (int.nat pos). }
      { rewrite -Hkey.
        auto using surjective_pairing.
      }
    }
    destruct HmodsSome as [vm HmodsSome].
    rewrite HmodsSome.
    iSplit; last first.
    { iPureIntro.
      rewrite Hmods_wsetL in HmodsSome.
      apply elem_of_list_lookup_2 in Hlookup.
      apply (elem_of_list_fmap_1 fst) in Hlookup.
      rewrite (surjective_pairing went.1) in Hlookup.
      rewrite Hkey in Hlookup.
      apply elem_of_list_to_map_1 in Hlookup; last auto.
      unfold wrent_to_key_dbval in HmodsSome.
      simpl in HmodsSome.
      rewrite list_fmap_compose list_to_map_fmap lookup_fmap in HmodsSome.
      rewrite Hlookup in HmodsSome.
      inversion HmodsSome.
      unfold to_dbval.
      destruct went.1.2.1; auto.
    }
    iDestruct ("HwsetL_close" with "HwsetL") as "HwsetL".
    eauto 20 with iFrame.
  }

  (***********************************************************)
  (* idx := txn.idx                                          *)
  (* tuple := idx.GetTuple(key)                              *)
  (* val, ret := tuple.ReadVersion(txn.tid)                  *)
  (* return val, ret == common.RET_SUCCESS                   *)
  (***********************************************************)
  iDestruct ("HwsetL_close" with "HwsetL") as "HwsetL".
  wp_loadField.
  wp_pures.
  wp_apply (wp_index__GetTuple with "HidxRI").
  iIntros (tuple) "#HtupleRI".
  wp_pures.
  wp_loadField.
  wp_apply (wp_tuple__ReadVersion with "HtupleRI Hactive").
  clear Heqb found.
  iIntros (val ret) "[Hactive Hview_ptsto']".
  wp_pures.
  iApply "HΦ".
  iModIntro.
  rewrite /spec_get.
  assert (HmodsNone : mods !! k = None).
  { destruct Hmatch as [[_ Hnotin] | [contra _]]; last congruence.
    rewrite Hmods_wsetL.
    apply not_elem_of_list_to_map.
    by rewrite wrent_to_key_dbval_key_fmap.
  }
  rewrite HmodsNone.
  destruct (view !! k) eqn:Eqlookup.
  { (* Proving the second case of `spec_get` (write set misses / non-first read). *)
    iDestruct (big_sepM_lookup_acc _ view k d with "[Hview]") as "[Hview_ptsto Hview_close]"; [auto | auto |].
    simpl.
    iSplit; last first.
    { unfold post_tuple__ReadVersion.
      iDestruct (case_tuple__ReadVersion with "Hview_ptsto'") as "[%H | %H]"; rewrite H.
      - iDestruct (view_ptsto_agree with "Hview_ptsto Hview_ptsto'") as %->.
        case_bool_decide; first done.
        apply u64_val_ne in H0.
        contradiction.
      - iDestruct (view_ptsto_agree with "Hview_ptsto Hview_ptsto'") as %->.
        case_bool_decide; last done.
        inversion H0.
        rewrite H2 in H.
        inversion H.
    }
    iDestruct ("Hview_close" with "Hview_ptsto") as "Hview".
    iExists _.
    iFrame "% Hmods Hview".
    do 5 iExists _.
    iFrame "HtxnmgrRI HidxRI".
    (* [eauto 20 with iFrame] very slow *)
    eauto 10 with iFrame.
  }
  { (* Proving the first case of `spec_get` (write set misses / first read). *)
    iExists _.
    iSplit; last done.
    iExists _.
    iFrame "Hmods".
    iSplitL "Hview Hview_ptsto'".
    { unfold post_tuple__ReadVersion.
      iDestruct (case_tuple__ReadVersion with "Hview_ptsto'") as "[%H | %H]"; rewrite H.
      - iApply big_sepM_insert; first done.
        iFrame "Hview".
        case_bool_decide; first done.
        apply u64_val_ne in H0.
        contradiction.
      - iApply big_sepM_insert; first done.
        iFrame "Hview".
        case_bool_decide; last done.
        inversion H0.
        rewrite H2 in H.
        inversion H.
    }
    eauto 20 with iFrame.
  }
Qed.

Definition spec_update txn view mods k v γ : iProp Σ :=
  is_txn txn view (<[k := v]> mods) γ.

Local Lemma NoDup_app_commute (A : Type) (l1 l2 : list A) :
  NoDup (l1 ++ l2) -> NoDup (l2 ++ l1).
Proof.
  intros H.
  apply NoDup_app in H as (H1 & H2 & H3).
  apply NoDup_app.
  split; first done.
  split; last done.
  intros x Hl2 Hl1.
  apply H2 in Hl1.
  contradiction.
Qed.

(*****************************************************************)
(* func (txn *Txn) Put(key, val uint64) bool                     *)
(*****************************************************************)
Theorem wp_txn__Put txn (k : u64) (v : u64) (view mods : gmap u64 dbval) γ :
  {{{ is_txn txn view mods γ }}}
    Txn__Put #txn #k #v
  {{{ (ok : bool), RET #ok; if ok
                          then spec_update txn view mods k (Value v) γ
                          else is_txn txn view mods γ
  }}}.
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
  (*     went := &txn.wset[pos]                              *)
  (*     went.val = DBVal{                                   *)
  (*         tomb : false,                                   *)
  (*         val  : val,                                     *)
  (*     }                                                   *)
  (*     return true                                         *)
  (* }                                                       *)
  (***********************************************************)
  iDestruct (slice.is_slice_small_acc with "HwsetL") as "[HwsetS HwsetL]".
  wp_if_destruct.
  { wp_loadField.
    destruct Hmatch as [[contra _] | [_ [went [HSome Hkey]]]]; first congruence.
    wp_lam.
    wp_pures.
    
    (* Handling [SliceRef]; a spec would help. *)
    wp_apply (wp_slice_len).
    iDestruct (is_slice_small_sz with "HwsetS") as "%HwsetSz".
    rewrite fmap_length in HwsetSz.
    wp_if_destruct; first last.
    { destruct Heqb0.
      apply lookup_lt_Some in HSome.
      rewrite HwsetSz in HSome.
      word.
    }
    wp_apply (wp_slice_ptr).
    wp_pures.
    rewrite /is_slice_small.
    iDestruct "HwsetS" as "[HwsetA %HwsetLen]".
    iDestruct (update_array (off:=int.nat pos) with "HwsetA") as "[HwsetP HwsetA]".
    { rewrite list_lookup_fmap.
      rewrite HSome.
      done.
    }
    iDestruct (struct_fields_split with "HwsetP") as "HwsetP".
    iNamed "HwsetP".
    wp_apply (wp_storeField with "[val]"); first auto.
    { iNext.
      iExactEq "val".
      do 3 f_equal.
      word.
    }
    iIntros "val".
    word_cleanup.
    set wentR := (wset.(Slice.ptr) +ₗ[_] (int.Z pos)).
    set went' := (went.1.1, (false, v), went.2).
    iDestruct (struct_fields_split wentR 1%Qp WrEnt (wrent_to_val went')
                with "[key val tuple]") as "HwsetP".
    { rewrite /struct_fields.
      iFrame.
      done.
    }
    iDestruct ("HwsetA" with "HwsetP") as "HwsetA".
    iDestruct ("HwsetL" with "[HwsetA]") as "HwsetL".
    { iFrame.
      iPureIntro.
      rewrite -HwsetLen.
      rewrite insert_length.
      done.
    }
    wp_pures.
    iApply "HΦ".
    iModIntro.
    unfold spec_update.
    
    (* Proving for the case where the key has been read or written. *)
    unfold is_txn.
    iExists _.
    iFrame "Hview".
    iSplitL "Hmods".
    { iApply (big_sepM_insert_override_2 _ _ _ (to_dbval went.1.2) with "[Hmods]"); [| auto | auto].
      rewrite Hmods_wsetL.
      apply elem_of_list_to_map_1; first by apply NoDup_wrent_to_key_dbval.
      apply elem_of_list_fmap.
      exists went.
      split; last by apply elem_of_list_lookup_2 with (int.nat pos).
      unfold wrent_to_key_dbval.
      by rewrite -Hkey.
    }
    do 5 iExists _.
    iFrame "# ∗".
    iSplit; first done.
    iSplit; first by rewrite -list_fmap_insert.
    iSplit.
    { iPureIntro.
      do 2 rewrite list_fmap_insert.
      subst went'.
      simpl.
      replace (<[ _ := _ ]> wsetL.*1.*1) with wsetL.*1.*1; first done.
      symmetry.
      apply list_insert_id.
      do 2 rewrite list_lookup_fmap.
      by rewrite HSome.
    }
    {
      iPureIntro.
      rewrite Hmods_wsetL.
      rewrite list_fmap_insert.
      subst went'.
      simpl.
      (* Related premises: [HSome], [Hkey], [HwsetLND], [Hmods_wsetL]. *)
      subst k.
      apply list_to_map_insert with (to_dbval went.1.2); first by apply NoDup_wrent_to_key_dbval.
      rewrite list_lookup_fmap.
      by rewrite HSome.
    }
  }
  iDestruct ("HwsetL" with "HwsetS") as "HwsetL".

  (***********************************************************)
  (* idx := txn.idx                                          *)
  (* tuple := idx.GetTuple(key)                              *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_index__GetTuple with "HidxRI").
  iIntros (tuple) "#HtupleRI".
  wp_pures.
  
  (***********************************************************)
  (* ret := tuple.Own(txn.tid)                                *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_tuple__Own with "HtupleRI Hactive").
  iIntros (ret) "[Hactive Hmods_token]".
  wp_pures.
  
  (***********************************************************)
  (* if ret != common.RET_SUCCESS {                          *)
  (*     return false                                        *)
  (* }                                                       *)
  (***********************************************************)
  wp_if_destruct.
  { iModIntro.
    iApply "HΦ".
    unfold is_txn.
    iExists _.
    iFrame "% Hmods Hview".
    do 5 iExists _.
    iFrame "HtxnmgrRI HidxRI".
    eauto 10 with iFrame.
  }

  (**************************************************************************)
  (* dbval := DBVal{                                                        *)
  (*     tomb : false,                                                      *)
  (*     val  : val,                                                        *)
  (* }                                                                      *)
  (* txn.wset = append(txn.wset, WrEnt{key: key, val: dbval, tuple: tuple}) *)
  (**************************************************************************)
  wp_pures.
  wp_loadField.
  wp_apply (wp_SliceAppend' with "[HwsetL]"); [auto 10 | auto 10 | auto |].
  iIntros (wset') "HwsetL".
  wp_storeField.
  
  (***********************************************************)
  (* return true                                             *)
  (***********************************************************)
  iModIntro.
  iApply "HΦ".
  rewrite /spec_update.
  destruct Hmatch as [[_ Hnotin] | [contra _]]; last congruence.
  set wsetL' := (wsetL ++ [(k, (false, v), tuple)]).
  set mods := (list_to_map _).
  assert (HmodsNone : mods !! k = None).
  { apply not_elem_of_list_to_map.
    by rewrite wrent_to_key_dbval_key_fmap.
  }
  iExists _.
  iFrame "Hview".
  iSplitL "Hmods Hmods_token".
  { iApply big_sepM_insert; [done | iFrame]. }
  
  do 4 iExists _.
  iExists wsetL'.
  iFrame "HtxnmgrRI HidxRI".
  iFrame "# ∗".
  iSplit; first done.
  iSplitL "HwsetL"; first by rewrite fmap_app.
  iSplit.
  { iPureIntro.
    do 2 rewrite fmap_app.
    simpl.
    apply NoDup_app_commute.
    apply NoDup_app.
    split; first by apply NoDup_singleton.
    split; last done.
    intros x H.
    apply elem_of_list_singleton in H.
    by subst x.
  }
  { iPureIntro.
    symmetry.
    subst mods.
    subst wsetL'.
    rewrite fmap_app.
    apply list_to_map_snoc.
    by rewrite wrent_to_key_dbval_key_fmap.
  }
Qed.

(*****************************************************************)
(* func (txn *Txn) Delete(key uint64) bool                       *)
(*****************************************************************)
Theorem wp_txn__Delete txn (k : u64) (v : u64) (view mods : gmap u64 dbval) γ :
  {{{ is_txn txn view mods γ }}}
    Txn__Delete #txn #k
  {{{ (ok : bool), RET #ok; if ok
                          then spec_update txn view mods k Nil γ
                          else is_txn txn view mods γ
  }}}.
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
  (*     went := &txn.wset[pos]                              *)
  (*     went.val = DBVal{                                   *)
  (*         tomb : true,                                    *)
  (*     }                                                   *)
  (*     return true                                         *)
  (* }                                                       *)
  (***********************************************************)
  iDestruct (slice.is_slice_small_acc with "HwsetL") as "[HwsetS HwsetL]".
  wp_if_destruct.
  { wp_loadField.
    destruct Hmatch as [[contra _] | [_ [went [HSome Hkey]]]]; first congruence.
    wp_lam.
    wp_pures.
    
    (* Handling [SliceRef]; a spec would help. *)
    wp_apply (wp_slice_len).
    iDestruct (is_slice_small_sz with "HwsetS") as "%HwsetSz".
    rewrite fmap_length in HwsetSz.
    wp_if_destruct; first last.
    { destruct Heqb0.
      apply lookup_lt_Some in HSome.
      rewrite HwsetSz in HSome.
      word.
    }
    wp_apply (wp_slice_ptr).
    wp_pures.
    rewrite /is_slice_small.
    iDestruct "HwsetS" as "[HwsetA %HwsetLen]".
    iDestruct (update_array (off:=int.nat pos) with "HwsetA") as "[HwsetP HwsetA]".
    { rewrite list_lookup_fmap.
      rewrite HSome.
      done.
    }
    iDestruct (struct_fields_split with "HwsetP") as "HwsetP".
    iNamed "HwsetP".
    wp_apply (wp_storeField with "[val]"); first auto.
    { iNext.
      iExactEq "val".
      do 3 f_equal.
      word.
    }
    iIntros "val".
    word_cleanup.
    set wentR := (wset.(Slice.ptr) +ₗ[_] (int.Z pos)).
    set went' := (went.1.1, (true, (U64 0)), went.2).
    iDestruct (struct_fields_split wentR 1%Qp WrEnt (wrent_to_val went')
                with "[key val tuple]") as "HwsetP".
    { rewrite /struct_fields.
      iFrame.
      done.
    }
    iDestruct ("HwsetA" with "HwsetP") as "HwsetA".
    iDestruct ("HwsetL" with "[HwsetA]") as "HwsetL".
    { iFrame.
      iPureIntro.
      rewrite -HwsetLen.
      rewrite insert_length.
      done.
    }
    wp_pures.
    iApply "HΦ".
    iModIntro.
    unfold spec_update.
    
    (* Proving for the case where the key has been read or written. *)
    unfold is_txn.
    iExists _.
    iFrame "Hview".
    iSplitL "Hmods".
    { iApply (big_sepM_insert_override_2 _ _ _ (to_dbval went.1.2) with "[Hmods]"); [| auto | auto].
      rewrite Hmods_wsetL.
      apply elem_of_list_to_map_1; first by apply NoDup_wrent_to_key_dbval.
      apply elem_of_list_fmap.
      exists went.
      split; last by apply elem_of_list_lookup_2 with (int.nat pos).
      unfold wrent_to_key_dbval.
      by rewrite -Hkey.
    }
    do 5 iExists _.
    iFrame "# ∗".
    iSplit; first done.
    iSplit; first by rewrite -list_fmap_insert.
    iSplit.
    { iPureIntro.
      do 2 rewrite list_fmap_insert.
      subst went'.
      simpl.
      replace (<[ _ := _ ]> wsetL.*1.*1) with wsetL.*1.*1; first done.
      symmetry.
      apply list_insert_id.
      do 2 rewrite list_lookup_fmap.
      by rewrite HSome.
    }
    {
      iPureIntro.
      rewrite Hmods_wsetL.
      rewrite list_fmap_insert.
      subst went'.
      simpl.
      (* Related premises: [HSome], [Hkey], [HwsetLND], [Hmods_wsetL]. *)
      subst k.
      apply list_to_map_insert with (to_dbval went.1.2); first by apply NoDup_wrent_to_key_dbval.
      rewrite list_lookup_fmap.
      by rewrite HSome.
    }
  }
  iDestruct ("HwsetL" with "HwsetS") as "HwsetL".

  (***********************************************************)
  (* idx := txn.idx                                          *)
  (* tuple := idx.GetTuple(key)                              *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_index__GetTuple with "HidxRI").
  iIntros (tuple) "#HtupleRI".
  wp_pures.
  
  (***********************************************************)
  (* ret := tuple.Own(txn.tid)                                *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_tuple__Own with "HtupleRI Hactive").
  iIntros (ret) "[Hactive Hmods_token]".
  wp_pures.
  
  (***********************************************************)
  (* if ret != common.RET_SUCCESS {                          *)
  (*     return false                                        *)
  (* }                                                       *)
  (***********************************************************)
  wp_if_destruct.
  { iModIntro.
    iApply "HΦ".
    unfold is_txn.
    iExists _.
    iFrame "% Hmods Hview".
    do 5 iExists _.
    iFrame "HtxnmgrRI HidxRI".
    eauto 10 with iFrame.
  }

  (**************************************************************************)
  (* dbval := DBVal{                                                        *)
  (*     tomb : true,                                                       *)
  (* }                                                                      *)
  (* txn.wset = append(txn.wset, WrEnt{key: key, val: dbval, tuple: tuple}) *)
  (**************************************************************************)
  wp_pures.
  wp_loadField.
  wp_apply (wp_SliceAppend' with "[HwsetL]"); [auto 10 | auto 10 | auto |].
  iIntros (wset') "HwsetL".
  wp_storeField.
  
  (***********************************************************)
  (* return true                                             *)
  (***********************************************************)
  iModIntro.
  iApply "HΦ".
  rewrite /spec_update.
  destruct Hmatch as [[_ Hnotin] | [contra _]]; last congruence.
  set wsetL' := (wsetL ++ [(k, (true, (U64 0)), tuple)]).
  set mods := (list_to_map _).
  assert (HmodsNone : mods !! k = None).
  { apply not_elem_of_list_to_map.
    by rewrite wrent_to_key_dbval_key_fmap.
  }
  iExists _.
  iFrame "Hview".
  iSplitL "Hmods Hmods_token".
  { iApply big_sepM_insert; [done | iFrame]. }
  
  do 4 iExists _.
  iExists wsetL'.
  iFrame "HtxnmgrRI HidxRI".
  iFrame "# ∗".
  iSplit; first done.
  iSplitL "HwsetL"; first by rewrite fmap_app.
  iSplit.
  { iPureIntro.
    do 2 rewrite fmap_app.
    simpl.
    apply NoDup_app_commute.
    apply NoDup_app.
    split; first by apply NoDup_singleton.
    split; last done.
    intros x H.
    apply elem_of_list_singleton in H.
    by subst x.
  }
  { iPureIntro.
    symmetry.
    subst mods.
    subst wsetL'.
    rewrite fmap_app.
    apply list_to_map_snoc.
    by rewrite wrent_to_key_dbval_key_fmap.
  }
Qed.

(* The client is responsible for proving C holds on all the updated extensions of `view`. *)
Theorem wp_txn__Commit txn view mods γ :
  {{{ ∀ dbmap, ⌜view ⊆ dbmap → C dbmap → C (mods ∪ dbmap)⌝ ∗ is_txn txn view mods γ }}}
    Txn__Commit #txn
  {{{ RET #(); is_txn_uninit txn γ (* * sth about log *) }}}.
Admitted.

End heap.
