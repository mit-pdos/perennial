(* Import definitions/theorems of the Perennial framework with the disk FFI. *)
From Perennial.program_proof Require Export grove_prelude.
(* Import Coq model of our Goose program. *)
From Goose.github_com.mit_pdos.go_mvcc Require Import txn.
From Perennial.program_proof.mvcc Require Import mvcc_ghost mvcc_misc gc_proof index_proof tuple_proof wrbuf_proof.
(* prefer untyped slices *)
Import Perennial.goose_lang.lib.slice.slice.

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

(* TODO: [site_active_tids_half_auth γ sid (gset_to_gmap () (list_to_set tidsactiveL))] to remove [tidsactiveM] *)
Definition own_txnsite (txnsite : loc) (sid : u64) γ : iProp Σ := 
  ∃ (tidlast tidmin : u64) (tidsactive : Slice.t)
    (tidsactiveL : list u64) (tidsactiveM : gmap u64 unit),
    "Htidlast" ∷ txnsite ↦[TxnSite :: "tidLast"] #tidlast ∗
    "Hactive" ∷ txnsite ↦[TxnSite :: "tidsActive"] (to_val tidsactive) ∗
    "HactiveL" ∷ typed_slice.is_slice tidsactive uint64T 1 tidsactiveL ∗
    "HactiveAuth" ∷ site_active_tids_half_auth γ sid tidsactiveM ∗
    "%HactiveLM" ∷ ⌜(list_to_set tidsactiveL) = dom tidsactiveM⌝ ∗
    "%HactiveND" ∷ (⌜NoDup tidsactiveL⌝) ∗
    "HminAuth" ∷ site_min_tid_half_auth γ sid (int.nat tidmin) ∗
    "%HtidOrder" ∷ (⌜Forall (λ tid, int.Z tidmin ≤ int.Z tid ≤ int.Z tidlast) (tidlast :: tidsactiveL)⌝) ∗
    "%HtidFree" ∷ (∀ tid, ⌜int.Z tidlast < int.Z tid -> tid ∉ dom tidsactiveM⌝) ∗
    "_" ∷ True.
Local Hint Extern 1 (environments.envs_entails _ (own_txnsite _ _ _)) => unfold own_txnsite : core.

Definition is_txnsite (site : loc) (sid : u64) γ : iProp Σ := 
  ∃ (latch : loc),
    "#Hlatch" ∷ readonly (site ↦[TxnSite :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (own_txnsite site sid γ) ∗
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
    "#HsitesRP" ∷ ([∗ list] sid ↦ site ∈ sitesL, is_txnsite site sid γ) ∗
    "#Hinvgc" ∷ mvcc_inv_gc γ ∗
    "_" ∷ True.
Local Hint Extern 1 (environments.envs_entails _ (is_txnmgr _ _)) => unfold is_txnmgr : core.

Definition own_txn_impl (txn : loc) (tid : u64) (mods : dbmap) γ : iProp Σ :=
  ∃ (sid : u64) (wrbuf : loc) (idx txnmgr : loc),
    "Htid" ∷ txn ↦[Txn :: "tid"] #tid ∗
    "Hsid" ∷ txn ↦[Txn :: "sid"] #sid ∗
    "%HsidB" ∷ ⌜(int.Z sid) < N_TXN_SITES⌝ ∗
    "Hwrbuf" ∷ txn ↦[Txn :: "wrbuf"] #wrbuf ∗
    "HwrbufRP" ∷ own_wrbuf wrbuf mods ∗
    "#Hidx" ∷ readonly (txn ↦[Txn :: "idx"] #idx) ∗
    "#HidxRI" ∷ is_index idx γ ∗
    "#Htxnmgr" ∷ readonly (txn ↦[Txn :: "txnMgr"] #txnmgr) ∗
    "#HtxnmgrRI" ∷ is_txnmgr txnmgr γ ∗
    "Hactive" ∷ active_tid γ tid sid ∗
    "_" ∷ True.
Local Hint Extern 1 (environments.envs_entails _ (own_txn_impl _ _ _ _)) => unfold own_txn_impl : core.

Definition own_txn (txn : loc) γ : iProp Σ :=
  ∃ (tid : u64) (mods : dbmap),
    "Himpl" ∷ own_txn_impl txn tid mods γ.
Local Hint Extern 1 (environments.envs_entails _ (own_txn _ _)) => unfold own_txn : core.

Definition own_txn_uninit (txn : loc) γ : iProp Σ := 
  ∃ (tid sid : u64) (wrbuf : loc) (idx txnmgr : loc),
    "Htid" ∷ txn ↦[Txn :: "tid"] #tid ∗
    "Hsid" ∷ txn ↦[Txn :: "sid"] #sid ∗
    "%HsidB" ∷ ⌜(int.Z sid) < N_TXN_SITES⌝ ∗
    "Hwrbuf" ∷ txn ↦[Txn :: "wrbuf"] #wrbuf ∗
    "HwrbufRP" ∷ own_wrbuf wrbuf ∅ ∗
    "#Hidx" ∷ readonly (txn ↦[Txn :: "idx"] #idx) ∗
    "#HidxRI" ∷ is_index idx γ ∗
    "#Htxnmgr" ∷ readonly (txn ↦[Txn :: "txnMgr"] #txnmgr) ∗
    "#HtxnmgrRI" ∷ is_txnmgr txnmgr γ ∗
    "_" ∷ True.

(*****************************************************************)
(* func MkTxnMgr() *TxnMgr                                       *)
(*****************************************************************)
Theorem wp_MkTxnMgr :
  {{{ True }}}
    MkTxnMgr #()
  {{{ (γ : mvcc_names) (txnmgr : loc), RET #txnmgr; is_txnmgr txnmgr γ }}}.
Proof.
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

  iMod mvcc_ghost_init as (γ) "(HinvtupleO & Hvchains & HinvgcO & HactiveAuthAll & HminAuthAll)".
  iMod (inv_alloc mvccNTuple _ (mvcc_inv_tuple_def γ) with "[$HinvtupleO]") as "#Hinvtuple".
  iMod (inv_alloc mvccNGC _ (mvcc_inv_gc_def γ) with "[$HinvgcO]") as "#Hinvgc".
  
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
  set P := λ (n : u64), (∃ sitesL,
    "HsitesS" ∷ is_slice_small sites ptrT 1 (to_val <$> sitesL) ∗
    "%Hlength" ∷ (⌜Z.of_nat (length sitesL) = N_TXN_SITES⌝) ∗
    "#HsitesRP" ∷ ([∗ list] sid ↦ site ∈ (take (int.nat n) sitesL), is_txnsite site sid γ) ∗
    "Hsites" ∷ (txnmgr ↦[TxnMgr :: "sites"] (to_val sites)) ∗
    "HactiveAuthAll" ∷ ([∗ list] sid ∈ (drop (int.nat n) sids_all), site_active_tids_half_auth γ sid ∅) ∗
    "HminAuthAll" ∷ ([∗ list] sid ∈ (drop (int.nat n) sids_all), site_min_tid_half_auth γ sid 0))%I.
  wp_apply (wp_forUpto P _ _ (U64 0) (U64 N_TXN_SITES) with "[] [HsitesS $sites $HiRef HactiveAuthAll HminAuthAll]"); first done.
  { clear Φ latch.
    iIntros (i Φ) "!> (Hloop & HiRef & %Hbound) HΦ".
    iNamed "Hloop".
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
    (* wp_apply (wp_NewSlice (V:=u64)). *)
    wp_apply (wp_NewSliceWithCap (V:=u64)); first word.
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
    
    rewrite (drop_S _ i); last first.
    { unfold sids_all, N_TXN_SITES.
      rewrite list_lookup_fmap.
      rewrite lookup_seqZ_lt; last word.
      simpl. f_equal. word.
    }
    iDestruct (big_sepL_cons with "HactiveAuthAll") as "[HactiveAuth HactiveAuthAll]".
    iDestruct (big_sepL_cons with "HminAuthAll") as "[HminAuth HminAuthAll]".
    iMod (readonly_alloc_1 with "latch") as "#Hlatch".
    iMod (alloc_lock mvccN _ latch (own_txnsite site i γ) with "[$Hfree] [-HsitesS HsitesRP HactiveAuthAll HminAuthAll]") as "#Hlock".
    { iNext.
      unfold own_txnsite.
      iExists (U64 0), (U64 0), (Slice.mk active 0 8), [], ∅.
      iFrame "% ∗".
      iPureIntro.
      split; first set_solver.
      split; first apply NoDup_nil_2.
      split; [by apply Forall_singleton | set_solver].
    }
    iModIntro.
    rewrite -list_fmap_insert.
    iExists _.
    iFrame.
    rewrite insert_length.
    iSplit; first done.
    replace (int.nat (word.add i 1)) with (S (int.nat i)); last word.
    iFrame.
    rewrite (take_S_r _ _ site); last first.
    { apply list_lookup_insert. word. }
    iApply (big_sepL_app).
    iSplitL "HsitesRP".
    { by rewrite take_insert; last auto. }
    iApply (big_sepL_singleton).
    unfold is_txnsite.
    rewrite take_length_le; last first.
    { rewrite insert_length. word. }
    (* Set Printing Coercions. *)
    replace (U64 _) with i by word.
    eauto with iFrame.
  }
  { iExists (replicate 64 null).
    auto with iFrame.
  }
  iIntros "[Hloop HiRef]".
  iNamed "Hloop".
  wp_pures.

  (***********************************************************)
  (* txnMgr.idx = index.MkIndex()                            *)
  (* txnMgr.gc = gc.MkGC(txnMgr.idx)                         *)
  (***********************************************************)
  wp_apply (wp_MkIndex γ with "Hinvtuple Hinvgc Hvchains").
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
  {{{ (txn : loc), RET #txn; own_txn_uninit txn γ }}}.
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
  (***********************************************************)
  wp_apply (wp_allocStruct); first auto 10.
  iIntros (txn) "Htxn".
  iDestruct (struct_fields_split with "Htxn") as "Htxn".
  iNamed "Htxn".
  simpl.
  wp_pures.
  
  (***********************************************************)
  (* txn.wrbuf = wrbuf.MkWrBuf                               *)
  (***********************************************************)
  wp_apply (wp_MkWrBuf).
  iIntros (wrbuf) "HwrbufRP".
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
  unfold own_txn_uninit.
  do 5 iExists _.
  iFrame "∗ %".
  iFrame "HidxRI Hidx_txn Htxnmgr_txn".
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
  iIntros (tidRef) "Htid".
  wp_pures.

  (***********************************************************)
  (* tid = GetTSC()                                          *)
  (***********************************************************)
  (* This is a hack *)
  iMod tsc_lb_0 as "Hlb".
  wp_apply (wp_GetTSC).
  (* XXX: We're wasting the fupd here since we're not opening any invariant. *)
  iApply ncfupd_mask_intro; first done.
  iIntros "HfupdC".
  iExists 0%nat.
  iFrame.
  iNext.
  iIntros (new_time) "[%Hnew Hlb]".
  iMod "HfupdC".
  iModIntro.
  iIntros "_".

  (************************************************************************)
  (* tid = ((tid + config.N_TXN_SITES) & ^(config.N_TXN_SITES - 1)) + sid *)
  (************************************************************************)
  wp_store.
  wp_load.
  wp_store.
  wp_pures.
  set tid := (word.add _ _).

  (***********************************************************)
  (* for GetTSC() <= tid {                                   *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool), (if b then True else tsc_lb (int.nat tid))%I.
  wp_apply (wp_forBreak_cond P).
  { admit. }
  { done. }
  iIntros "HP". unfold P. clear P.
  wp_load.

  (***********************************************************)
  (* return tid                                              *) 
  (***********************************************************)
  iApply "HΦ".
  iModIntro.
  iPureIntro.
  done.
Admitted.

(*****************************************************************)
(* func (txnMgr *TxnMgr) activate(sid uint64) uint64             *)
(*****************************************************************)
Theorem wp_txnMgr__activate (txnmgr : loc) (sid : u64) γ :
  is_txnmgr txnmgr γ -∗
  {{{ ⌜(int.Z sid) < N_TXN_SITES⌝ }}}
    TxnMgr__activate #txnmgr #sid
  {{{ (tid : u64), RET #tid; active_tid γ tid sid }}}.
Proof.
  iIntros "#Htxnmgr !>" (Φ) "%HsitesBound HΦ".
  iNamed "Htxnmgr".
  wp_call.
  
  (***********************************************************)
  (* site := txnMgr.sites[sid]                               *)
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

  (***********************************************************)
  (* site.latch.Lock()                                       *)
  (***********************************************************)
  iDestruct (big_sepL_lookup with "HsitesRP") as "HsiteRP"; first done.
  iClear (latch) "Hlatch Hlock".
  iNamed "HsiteRP".
  wp_loadField.
  wp_apply (acquire_spec with "[$Hlock]").
  iIntros "[Hlocked HsiteOwn]".
  replace (U64 (Z.of_nat _)) with sid by word. 
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
  set P := λ (b : bool), (∃ (tidnew : u64),
             "Htidlast" ∷ site ↦[TxnSite :: "tidLast"] #tidlast ∗
             "HtidRef" ∷ tidRef ↦[uint64T] #tidnew ∗
             "%Hexit" ∷ if b then True else ⌜(int.Z tidnew) > (int.Z tidlast)⌝)%I.
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
  (* machine.Assume(tid < 18446744073709551615)              *)
  (***********************************************************)
  wp_load.
  wp_apply wp_Assume.
  iIntros "%Htidmax".
  apply bool_decide_eq_true_1 in Htidmax.
  
  (***********************************************************)
  (* site.tidLast = tid                                      *)
  (* site.tidsActive = append(site.tidsActive, tid)          *)
  (***********************************************************)
  wp_load.
  wp_storeField.
  wp_load.
  wp_loadField.
  wp_apply (typed_slice.wp_SliceAppend (V := u64) with "HactiveL").
  iIntros (tidsactive') "HactiveL".
  wp_storeField.
  wp_loadField.

  (* The local set of active tids is added with [tid], prove [tid ≥ tidmin]. *)

  (* Open the global invariant. *)
  iApply fupd_wp.
  iInv "Hinvgc" as ">HinvgcO" "HinvgcC".
  (* unfold mvcc_inv_gc_def. *)
  iDestruct (big_sepL_lookup_acc with "HinvgcO") as "[HinvgcO HinvgcOAcc]".
  { by apply sids_all_lookup. }
  iDestruct "HinvgcO" as (tidsM tidmin') "(HactiveAuth' & HminAuth' & %Hmin)".
  (* Update the set of active tids. *)
  iDestruct (site_active_tids_agree with "HactiveAuth' HactiveAuth") as %->.
  iMod (site_active_tids_insert tidnew with "HactiveAuth' HactiveAuth") as "(HactiveAuth' & HactiveAuth & HactiveFrag)".
  { apply HtidFree. word. }
  set tidsactiveM' := <[tidnew := tt]>tidsactiveM.
  (* Agree on the minimal tid. *)
  iDestruct (site_min_tid_agree with "HminAuth' HminAuth") as "%Emin".
  rewrite Emin. rewrite Emin in Hmin.
  clear Emin tidmin'.
  (* Close the global invariant. *)
  iDestruct ("HinvgcOAcc" with "[HactiveAuth' HminAuth']") as "HinvgcO".
  { do 2 iExists _.
    iFrame "HactiveAuth' HminAuth'".
    subst tidsactiveM'.
    rewrite dom_insert_L.

    iPureIntro.
    intros tidx Helem.
    apply elem_of_union in Helem.

    destruct Helem; last auto.
    apply elem_of_singleton in H.
    subst tidx.
    apply Forall_inv in HtidOrder.
    trans (int.nat tidlast); word.
  }
  iMod ("HinvgcC" with "[HinvgcO]") as "_"; first done.
  iModIntro.
    
  (***********************************************************)
  (* site.latch.Unlock()                                     *)
  (***********************************************************)
  wp_apply (release_spec with "[-HΦ HtidRef HactiveFrag]").
  { iFrame "Hlock Hlocked".
    iNext.
    do 5 iExists _.
    iFrame "% ∗".
    iSplit.
    { (* Prove [HactiveLM]. *)
      iPureIntro.
      (* Q: Why can't rewrite list_to_set_snoc? How to rewrite ≡? *)
      rewrite list_to_set_app_L.
      simpl.
      subst tidsactiveM'.
      rewrite dom_insert_L.
      set_solver.
    }
    iPureIntro.
    split.
    { (* Prove [HactiveND]. *)
      apply NoDup_app.
      split; first done.
      split; last apply NoDup_singleton.
      intros tidx Hin.
      rewrite -HactiveLM in HtidFree.
      setoid_rewrite not_elem_of_list_to_set in HtidFree.
      assert (contra : tidnew ∉ tidsactiveL).
      { apply HtidFree. word. }
      set_solver.
    }
    split.
    { (* Prove [HtidOrder]. *)
      apply Forall_cons.
      split.
      { split; last done.
        apply Forall_inv in HtidOrder. word.
      }
      apply Forall_app.
      split; last first.
      { apply Forall_singleton.
        split; last done.
        apply Forall_inv in HtidOrder. word.
      }
      apply Forall_inv_tail in HtidOrder.
      apply (Forall_impl _ _ _ HtidOrder).
      word.
    }
    split; last done.
    { (* Prove [HtidlastNotin]. *)
      simpl.
      intros tidx Htidx.
      subst tidsactiveM'.
      rewrite dom_insert_L.
      apply not_elem_of_union.
      split.
      - unfold not. intros contra.
        rewrite elem_of_singleton in contra.
        rewrite contra in Htidx. word.
      - apply HtidFree. word.
    }
  }
  wp_pures.
  wp_load.
  
  (***********************************************************)
  (* return tid                                              *)
  (***********************************************************)
  iApply "HΦ".
  iModIntro.
  iFrame.
  iPureIntro. word.
Qed.

(*****************************************************************)
(* func swapWithEnd(xs []uint64, i uint64)                       *)
(*****************************************************************)
Local Theorem wp_swapWithEnd (xsS : Slice.t) (xs : list u64) (i : u64) (x : u64) :
  {{{ typed_slice.is_slice xsS uint64T 1 xs ∧ (⌜xs !! (int.nat i) = Some x⌝) }}}
    swapWithEnd (to_val xsS) #i
  {{{ (xs' : list u64), RET #(); typed_slice.is_slice xsS uint64T 1 (xs' ++ [x]) ∧
                                 (⌜xs' ≡ₚ delete (int.nat i) xs⌝)
  }}}.
Proof.
  iIntros (Φ) "[HtidsS %Hlookup] HΦ".
  wp_call.
  iDestruct (is_slice_sz with "HtidsS") as "%HtidsSz".
  iDestruct (typed_slice.is_slice_small_acc with "HtidsS") as "[HtidsS HtidsC]".
  rewrite fmap_length in HtidsSz.
  assert (Hgz : int.Z xsS.(Slice.sz) > 0).
  { apply lookup_lt_Some in Hlookup. word. }

  (***********************************************************)
  (* tmp := xs[len(xs) - 1]                                  *)
  (***********************************************************)
  wp_apply wp_slice_len.
  wp_pures.
  set idxlast := word.sub _ _.
  assert (Hidxlast : int.Z idxlast = (int.Z xsS.(Slice.sz)) - 1).
  { subst idxlast. word. }
  assert (HlookupLast : (int.nat idxlast < length xs)%nat) by word.
  apply list_lookup_lt in HlookupLast as [xlast HlookupLast].
  (* wp_apply (typed_slice.wp_SliceGet (V:=u64) with "[HtidsS]"). *)
  wp_apply (typed_slice.wp_SliceGet with "[$HtidsS]").
  { iFrame.
    iPureIntro.
    by rewrite HlookupLast.
  }
  iIntros "HtidsS".
    
  (***********************************************************)
  (* xs[len(xs) - 1] = xs[i]                                 *)
  (***********************************************************)
  wp_pures.
  wp_apply (typed_slice.wp_SliceGet with "[$HtidsS]").
  { iFrame.
    iPureIntro.
    by rewrite Hlookup.
  }
  iIntros "HtidsS".
  wp_apply wp_slice_len.
  wp_pures.
  wp_apply (typed_slice.wp_SliceSet with "[$HtidsS]").
  { iFrame.
    iPureIntro.
    by rewrite HlookupLast.
  }
  iIntros "HtidsS".
  wp_pures.

  (***********************************************************)
  (* xs[i] = tmp                                             *)
  (***********************************************************)
  wp_apply (typed_slice.wp_SliceSet with "[$HtidsS]").
  { iFrame.
    iPureIntro.
    apply lookup_lt_is_Some_2.
    rewrite insert_length.
    by eapply lookup_lt_Some.
  }
  iIntros "HtidsS".
  iDestruct ("HtidsC" with "HtidsS") as "HtidsS".
  wp_pures.

  destruct (decide (pred (length xs) ≤ int.nat i)%nat).
  - (* Case: [i = idxlast]. *)
    iApply "HΦ".
    iModIntro.
    subst idxlast.
    replace (int.nat (word.sub _ _)) with (pred (length xs)) in *; last word.
    apply lookup_lt_Some in Hlookup as Hlt.
    { assert (Ei : (int.nat i) = pred (length xs)) by lia.
      rewrite Ei.
      rewrite list_insert_insert.
      rewrite list_insert_at_end; last set_solver.
      replace x with xlast; last first.
      { rewrite Ei in Hlookup. set_solver. }
      iFrame.
      iPureIntro.
      rewrite delete_take_drop.
      replace (drop _ _) with ([] : list u64); last first.
      { replace (S _) with (length xs); last lia. by rewrite drop_all. }
      rewrite app_nil_r.
      by rewrite removelast_firstn_len.
    }
  - (* Case: [i ≠ idxlast]. *)
    iApply "HΦ".
    iModIntro.
    apply Nat.nle_gt in n.
    replace (int.nat (word.sub _ _)) with (pred (length xs)); last word.
    rewrite list_insert_at_end; last set_solver.
    rewrite insert_app_l; last first.
    { rewrite removelast_firstn_len. rewrite take_length_le; word. }
    iFrame.
    iPureIntro.
    apply list_swap_with_end with x; [done | | done].
    rewrite -HlookupLast.
    replace (int.nat idxlast) with (pred (length xs)); last word.
    apply last_lookup.
Qed.

(*****************************************************************)
(* func findTID(tid uint64, tids []uint64) uint64                *)
(*****************************************************************)
Local Theorem wp_findTID (tid : u64) (tidsS : Slice.t) (tids : list u64) :
  {{{ typed_slice.is_slice tidsS uint64T 1 tids ∗ ⌜tid ∈ tids⌝ }}}
    findTID #tid (to_val tidsS)
  {{{ (idx : u64), RET #idx; typed_slice.is_slice tidsS uint64T 1 tids ∧
                             (⌜tids !! (int.nat idx) = Some tid⌝)
  }}}.
Proof.
  iIntros (Φ) "[HtidsS %Helem] HΦ".
  wp_call.

  (***********************************************************)
  (* var idx uint64 = 0                                      *)
  (***********************************************************)
  wp_apply (wp_ref_to); first auto.
  iIntros (idxRef) "HidxRef".
  wp_pures.
  
  (***********************************************************)
  (* for {                                                   *)
  (*     tidx := tids[idx]                                   *)
  (*     if tid == tidx {                                    *)
  (*         break                                           *)
  (*     }                                                   *)
  (*     idx++                                               *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool), (∃ (idx : u64),
    "HidxRef" ∷ idxRef ↦[uint64T] #idx ∗
    "HtidsS" ∷  typed_slice.is_slice tidsS uint64T 1 tids ∗
    "%Hne" ∷ (⌜Forall (λ tidx, tidx ≠ tid) (take (int.nat idx) tids)⌝) ∗
    "%Hbound" ∷ ⌜(int.Z idx < Z.of_nat (length tids))⌝ ∗
    "%Hexit" ∷ (⌜if b then True else tids !! (int.nat idx) = Some tid⌝))%I.
  wp_apply (wp_forBreak P with "[] [HidxRef HtidsS]").
  { clear Φ.
    iIntros (Φ) "!> Hloop HΦ".
    iNamed "Hloop".
    wp_pures.
    wp_load.
    assert (Hlookup : (int.nat idx < length tids)%nat) by word.
    apply list_lookup_lt in Hlookup as [tidx Hlookup].
    iDestruct (is_slice_small_acc with "HtidsS") as "[HtidsS HtidsC]".
    wp_apply (wp_SliceGet with "[HtidsS]").
    { iFrame.
      iPureIntro.
      rewrite list_lookup_fmap.
      by rewrite Hlookup.
    }
    iIntros "[HtidsS %HtidsVT]".
    iDestruct ("HtidsC" with "HtidsS") as "HtidsS".
    wp_pures.
    wp_if_destruct.
    { iApply "HΦ". unfold P. eauto with iFrame. }
    wp_load.
    wp_store.
    iApply "HΦ".
    iModIntro.
    iExists _.
    iDestruct (is_slice_sz with "HtidsS") as "%HtidsSz".
    rewrite fmap_length in HtidsSz.
    iFrame "% ∗".
    iPureIntro.
    split.
    { replace (int.nat _) with (S (int.nat idx)); last word.
      rewrite (take_S_r _ _ tidx); last done.
      apply Forall_app_2; first done.
      apply Forall_singleton.
      apply u64_val_ne in Heqb.
      unfold not. intros H. rewrite H in Heqb. word.
    }
    { destruct (decide (int.Z idx < Z.of_nat (length tids) - 1)); first word.
      apply Znot_lt_ge in n.
      assert (Hexists: Exists (λ tidx : u64, tidx = tid) tids).
      { rewrite Exists_exists. by exists tid. }
      destruct (Exists_not_Forall (λ tidx : u64, tidx ≠ tid) tids).
      { apply (Exists_impl _ _ _ Hexists). auto. }
      replace tids with (take (S (int.nat idx)) tids); last first.
      { rewrite take_ge; [done | word]. }
      rewrite (take_S_r _ _ tidx); last done.
      apply Forall_app_2; first done.
      apply Forall_singleton.
      apply u64_val_ne in Heqb.
      unfold not. intros H. rewrite H in Heqb. word.
    }
  }
  { iExists _.
    iFrame.
    iPureIntro.
    split.
    { change (int.nat 0) with 0%nat. by rewrite take_0. }
    split; last done.
    { apply elem_of_list_lookup in Helem as [i Hlookup].
      apply lookup_lt_Some in Hlookup. word.
    }
  }
  iIntros "Hloop".
  iNamed "Hloop".
  wp_pures.
  
  (***********************************************************)
  (* return idx                                              *)
  (***********************************************************)
  wp_load.
  iApply "HΦ".
  by iFrame.
Qed.

(*****************************************************************)
(* func (txnMgr *TxnMgr) deactivate(sid uint64, tid uint64)      *)
(*****************************************************************)
Local Theorem wp_txnMgr__deactivate txnmgr (sid tid : u64) γ :
  is_txnmgr txnmgr γ -∗
  {{{ active_tid γ tid sid }}}
    TxnMgr__deactivate #txnmgr #sid #tid
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htxnmgr" (Φ) "!> Hactive HΦ".
  iNamed "Htxnmgr".
  wp_call.

  (***********************************************************)
  (* site := txnMgr.sites[sid]                               *)
  (***********************************************************)
  wp_loadField.
  iMod (readonly_load with "HsitesS") as (q) "HsitesS'".
  iDestruct "Hactive" as "[[HactiveFrag %Hbound] _]".
  list_elem sitesL (int.nat sid) as site.
  wp_apply (wp_SliceGet with "[$HsitesS']").
  { iPureIntro.
    rewrite list_lookup_fmap.
    by rewrite Hsite_lookup.
  }
  iIntros "[HsitesS' %HsiteVT]".
  wp_pures.

  (***********************************************************)
  (* site.latch.Lock()                                       *)
  (***********************************************************)
  iDestruct (big_sepL_lookup with "HsitesRP") as "HsiteRP"; first done.
  iClear (latch) "Hlatch Hlock".
  iNamed "HsiteRP".
  wp_loadField.
  wp_apply (acquire_spec with "[$Hlock]").
  iIntros "[Hlocked HsiteOwn]".
  replace (U64 (Z.of_nat _)) with sid by word. 
  iNamed "HsiteOwn".
  iDestruct (is_slice_sz with "HactiveL") as "%HactiveSz".
  rewrite fmap_length in HactiveSz.
  wp_pures.
  
  (*****************************************************************)
  (* idx := findTID(tid, site.tidsActive)                          *)
  (*****************************************************************)
  wp_loadField.
  iDestruct (site_active_tids_elem_of with "HactiveAuth HactiveFrag") as "%Hin".
  rewrite -HactiveLM elem_of_list_to_set in Hin.
  wp_apply (wp_findTID tid _ tidsactiveL with "[$HactiveL]"); first auto.
  iIntros (pos) "[HactiveL %Hlookup]".
  wp_pures.
  
  (*****************************************************************)
  (* swapWithEnd(site.tidsActive, idx)                             *)
  (*****************************************************************)
  wp_loadField.
  wp_apply (wp_swapWithEnd with "[HactiveL]"); first by iFrame.
  iIntros (tids) "[HactiveL %Hperm]".
  wp_pures.
  
  (*****************************************************************)
  (* site.tidsActive = site.tidsActive[:len(site.tidsActive) - 1]  *)
  (*****************************************************************)
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_loadField.
  iDestruct (is_slice_wf with "HactiveL") as "%HtidsactiveCap".
  wp_apply (wp_SliceTake).
  { apply lookup_lt_Some in Hlookup. word. }
  wp_storeField.
  wp_loadField.

  (* Open the global invariant to update the local active TIDs. *)
  iApply fupd_wp.
  iInv "Hinvgc" as ">HinvgcO" "HinvgcC".
  iDestruct (big_sepL_lookup_acc with "HinvgcO") as "[HinvgcO HinvgcOAcc]".
  { by apply sids_all_lookup. }
  iDestruct "HinvgcO" as (tidsM tidmin') "(HactiveAuth' & HminAuth' & %Hmin)".
  (* Update the set of active tids. *)
  iDestruct (site_active_tids_agree with "HactiveAuth' HactiveAuth") as %->.
  iMod (site_active_tids_delete tid with "HactiveFrag HactiveAuth' HactiveAuth") as "[HactiveAuth' HactiveAuth]".
  (* Close the global invariant. *)
  iDestruct ("HinvgcOAcc" with "[HactiveAuth' HminAuth']") as "HinvgcO".
  { do 2 iExists _.
    iFrame "HactiveAuth' HminAuth'".
    iPureIntro.
    rewrite dom_delete_L.
    set_solver.
  }
  iMod ("HinvgcC" with "[HinvgcO]") as "_"; first done.
  iModIntro.
  
  (*****************************************************************)
  (* site.latch.Unlock()                                           *)
  (*****************************************************************)
  wp_apply (release_spec with "[-HΦ]").
  { iFrame "Hlock Hlocked".
    iNext.
    set idxlast := (word.sub _ _).
    iExists _, _, _, tids, _.
    iFrame "Hactive".
    iFrame.
    assert (Hidxlast : int.nat idxlast = length tids).
    { subst idxlast.
      rewrite (Permutation_length Hperm).
      rewrite length_delete; last done.
      assert (H : (int.nat tidsactive.(Slice.sz) > 0)%nat).
      { rewrite -HactiveSz. apply lookup_lt_Some in Hlookup. lia. }
      rewrite HactiveSz. word.
    }
    iSplitL "HactiveL".
    { (* Prove [HactiveL]. *)
      unfold typed_slice.is_slice.
      unfold list.untype.
      iDestruct (is_slice_take_cap _ _ _ idxlast with "HactiveL") as "H".
      { rewrite fmap_length. rewrite last_length. word. }
      unfold named.
      iExactEq "H".
      rewrite -fmap_take.
      do 2 f_equal.
      replace (int.nat idxlast) with (length tids).
      apply take_app.
    }
    iSplit.
    { (* Prove [HactiveLM]. *)
      iPureIntro.
      rewrite (list_to_set_perm_L _ (delete (int.nat pos) tidsactiveL)); last done.
      rewrite dom_delete_L.
      rewrite -HactiveLM.
      rewrite delete_take_drop.
      apply take_drop_middle in Hlookup.
      rewrite <- Hlookup at 3.
      do 2 rewrite list_to_set_app_L.
      rewrite list_to_set_cons.
      set s1 := (list_to_set (take _ _)).
      set s2 := (list_to_set (drop _ _)).
      do 2 rewrite difference_union_distr_l_L.
      rewrite -Hlookup in HactiveND.
      apply NoDup_app in HactiveND as [_ [Hnotins1 Hnotins2]].
      apply NoDup_cons in Hnotins2 as [Hnotins2 _].
      replace (s1 ∖ {[tid]}) with s1 by set_solver.
      replace (s2 ∖ {[tid]}) with s2 by set_solver.
      set_solver.
    }
    iPureIntro.
    split.
    { (* Prove [HactiveND]. *)
      apply (NoDup_Permutation_proper _ _ Hperm).
      rewrite delete_take_drop.
      apply take_drop_middle in Hlookup.
      rewrite -Hlookup in HactiveND.
      apply NoDup_app in HactiveND as [HND1 [Hnotin1 HND2]].
      apply NoDup_cons in HND2 as [_ HND2].
      apply NoDup_app.
      split; first done.
      split; last done.
      set_solver.
    }
    split.
    { (* Prove [HtidOrder] *)
      apply Forall_cons_2; first by apply Forall_inv in HtidOrder.
      apply Forall_inv_tail in HtidOrder.
      apply (Forall_Permutation _ _ _ Hperm).
      by apply Forall_delete.
    }
    split; last done.
    { (* Prove [HtidFree]. *)
      simpl.
      intros tidx Htidx.
      apply not_elem_of_weaken with (dom tidsactiveM); last set_solver.
      auto.
    }
  }
  wp_pures.
  by iApply "HΦ".
Qed.

(*****************************************************************)
(* func (txnMgr *TxnMgr) getMinActiveTIDSite(sid uint64) uint64  *)
(*****************************************************************)
Theorem wp_txnMgr__getMinActiveTIDSite txnmgr (sid : u64) γ :
  is_txnmgr txnmgr γ -∗
  {{{ ⌜int.Z sid < int.Z N_TXN_SITES⌝ }}}
    TxnMgr__getMinActiveTIDSite #txnmgr #sid
  {{{ (tid : u64), RET #tid; site_min_tid_lb γ sid (int.nat tid) }}}.
Proof.
  iIntros "#Htxnmgr" (Φ) "!> %Hbound HΦ".
  iNamed "Htxnmgr".
  iMod (readonly_load with "HsitesS") as (q) "HsitesS'".
  wp_call.

  (***********************************************************)
  (* site := txnMgr.sites[sid]                               *)
  (***********************************************************)
  wp_loadField.
  list_elem sitesL (int.nat sid) as site.
  { revert HsitesLen. unfold N_TXN_SITES in *. word. }
  wp_apply (wp_SliceGet with "[$HsitesS']").
  { iPureIntro.
    rewrite list_lookup_fmap.
    by rewrite Hsite_lookup.
  }
  iIntros "[HsitesS' _]".
  wp_pures.
  
  (***********************************************************)
  (* site.latch.Lock()                                       *)
  (***********************************************************)
  iDestruct (big_sepL_lookup with "HsitesRP") as "HsiteRP"; first done.
  iClear (latch) "Hlatch Hlock".
  iNamed "HsiteRP".
  wp_loadField.
  wp_apply (acquire_spec with "[$Hlock]").
  iIntros "[Hlocked HsiteOwn]".
  replace (U64 (Z.of_nat _)) with sid by word. 
  iNamed "HsiteOwn".
  iDestruct (typed_slice.is_slice_sz with "HactiveL") as "%HtidsactiveSz".
  wp_pures.
  
  (***********************************************************)
  (* var tidnew uint64                                       *)
  (* tidnew = genTID(sid)                                    *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first done.
  iIntros (tidnewRef) "HtidnewRef".
  wp_pures.
  wp_apply (wp_genTID).
  iIntros (tidnew) "_".
  wp_store.
  wp_pures.
  
  (***********************************************************)
  (* for tid <= site.tidLast {                               *)
  (*     tid = genTID(sid)                                   *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool), (∃ (tidnew : u64),
             "Htidlast" ∷ site ↦[TxnSite :: "tidLast"] #tidlast ∗
             "HtidnewRef" ∷ tidnewRef ↦[uint64T] #tidnew ∗
             "%Hexit" ∷ if b then ⌜True⌝ else ⌜(int.Z tidnew) > (int.Z tidlast)⌝)%I.
  wp_apply (wp_forBreak_cond P with "[] [Htidlast HtidnewRef]").
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
  clear tidnew.
  iNamed "Hloop".
  wp_pures.
  
  (***********************************************************)
  (* site.tidLast = tidnew                                   *)
  (* var tidmin uint64 = tidnew                              *)
  (***********************************************************)
  wp_load.
  wp_storeField.
  wp_load.
  wp_apply (wp_ref_to); first auto.
  iIntros (tidminRef) "HtidminRef".
  wp_pures.

  (***********************************************************)
  (* for _, tid := range site.tidsActive {                   *)
  (*     if tid < tidmin {                                   *)
  (*         tidmin = tid                                    *)
  (*     }                                                   *)
  (* }                                                       *)
  (***********************************************************)
  iDestruct (is_slice_small_acc with "HactiveL") as "[HactiveS HactiveC]".
  wp_loadField.
  clear P.
  set P := λ (i : u64), (∃ (tidmin : u64), let tids := tidnew :: (take (int.nat i) tidsactiveL) in
    "HtidminRef" ∷ tidminRef ↦[uint64T] #tidmin ∗
    "%Helem" ∷ ⌜tidmin ∈ tids⌝ ∗
    "%HtidminLe" ∷ (⌜Forall (λ tid, int.Z tidmin ≤ int.Z tid) tids⌝))%I.
  wp_apply (typed_slice.wp_forSlice P _ _ _ _ _ tidsactiveL with "[] [HtidminRef $HactiveS]").
  { clear Φ.
    iIntros (i tidx Φ) "!> (Hloop & %Hbound' & %Hlookup) HΦ".
    iNamed "Hloop".
    wp_load.
    wp_if_destruct.
    - wp_store.
      iApply "HΦ".
      iModIntro.
      iExists _.
      iFrame.
      do 2 replace (int.nat (word.add i 1)) with (S (int.nat i)) by word.
      rewrite (take_S_r _ _ tidx); last done.
      iSplit; iPureIntro.
      { set_solver. }
      { rewrite app_comm_cons.
        rewrite Forall_app.
        split.
        { apply (Forall_impl _ _ _ HtidminLe). word. }
        apply Forall_singleton. done.
      }
    - iApply "HΦ".
      iModIntro.
      iExists _.
      iFrame.
      do 2 replace (int.nat (word.add i 1)) with (S (int.nat i)) by word.
      rewrite (take_S_r _ _ tidx); last done.
      iSplit; iPureIntro.
      { set_solver. }
      { rewrite app_comm_cons.
        rewrite Forall_app.
        split.
        { apply (Forall_impl _ _ _ HtidminLe). word. }
        apply Forall_singleton. word.
      }
  }
  { iExists _.
    iFrame.
    iPureIntro.
    rewrite take_0.
    rewrite Forall_forall.
    split; set_solver.
  }
  iIntros "[Hloop HactiveS]".
  iNamed "Hloop".
  rename tidmin0 into tidmin'.
  rewrite -HtidsactiveSz in Helem HtidminLe.
  rewrite firstn_all in Helem HtidminLe.

  (* Prove that we can safely update the local lower bound. *)
  assert (Hle : int.Z tidmin ≤ int.Z tidmin').
  { apply elem_of_cons in Helem.
    destruct Helem.
    - rewrite H.
      apply Forall_inv in HtidOrder. word.
    - apply Forall_inv_tail in HtidOrder.
      rewrite Forall_forall in HtidOrder.
      apply HtidOrder. done.
  }
  
  (* Open the global invariant to update [tidmin]. *)
  wp_apply (fupd_wp).
  iInv "Hinvgc" as ">HinvgcO" "HinvgcC".
  iDestruct (big_sepL_lookup_acc with "HinvgcO") as "[HinvgcO HinvgcOAcc]".
  { by apply sids_all_lookup. }
  iDestruct "HinvgcO" as (tidsM tidmin'') "(HactiveAuth' & HminAuth' & Hmin)".
  (* Agree on the set of active tids. *)
  iDestruct (site_active_tids_agree with "HactiveAuth' HactiveAuth") as %->.
  (* Update the minimal tid. *)
  iDestruct (site_min_tid_agree with "HminAuth' HminAuth") as %->.
  clear tidmin''.
  iMod (site_min_tid_update (int.nat tidmin') with "HminAuth' HminAuth") as "[HminAuth' HminAuth]"; first word.
  
  (* Close the global invariant. *)
  iDestruct ("HinvgcOAcc" with "[HactiveAuth' HminAuth' Hmin]") as "HinvgcO".
  { do 2 iExists _.
    iFrame "HactiveAuth' HminAuth'".
    iPureIntro.
    unfold set_Forall.
    apply Forall_inv_tail in HtidminLe.
    rewrite Forall_forall in HtidminLe.
    rewrite -HactiveLM.
    setoid_rewrite elem_of_list_to_set.
    intros ? Hx. specialize (HtidminLe _ Hx). word.
  }
  iMod ("HinvgcC" with "[HinvgcO]") as "_"; first done.
  iModIntro.

  (* Obtaining [site_min_tid_lb] for the postcondition. *)
  iDestruct (site_min_tid_witness with "HminAuth") as "#HminLb".
  
  (***********************************************************)
  (* site.latch.Unlock()                                     *)
  (* return tidmin                                           *)
  (***********************************************************)
  iDestruct ("HactiveC" with "HactiveS") as "HactiveL".
  wp_loadField.
  wp_apply (release_spec with "[-HΦ HtidminRef]").
  { iFrame "Hlock Hlocked".
    iNext.
    do 5 iExists _.
    iFrame "% ∗".
    iSplit; iPureIntro.
    { apply Forall_and.
      split; first done.
      apply Forall_cons.
      split; first word.
      apply Forall_inv_tail, Forall_and in HtidOrder.
      destruct HtidOrder as [_ HtidOrder].
      apply (Forall_impl _ _ _ HtidOrder).
      word.
    }
    split; last done.
    { intros tidx Hlt. apply HtidFree. word. }
  }
  wp_load.
  by iApply "HΦ".
Qed.

(*****************************************************************)
(* func (txnMgr *TxnMgr) getMinActiveTID() uint64                *)
(*****************************************************************)
Theorem wp_txnMgr__getMinActiveTID txnmgr γ :
  is_txnmgr txnmgr γ -∗
  {{{ True }}}
    TxnMgr__getMinActiveTID #txnmgr
  {{{ (tid : u64), RET #tid; min_tid_lb γ (int.nat tid) }}}.
Proof.
  iIntros "#Htxnmgr" (Φ) "!> _ HΦ".
  wp_call.
  
  (***********************************************************)
  (* var min uint64 = config.TID_SENTINEL                    *)
  (***********************************************************)
  wp_apply (wp_ref_to); first auto.
  iIntros (minRef) "HminRef".
  wp_pures.
    
  (***********************************************************)
  (* for sid := uint64(0); sid < config.N_TXN_SITES; sid++ { *)
  (*     tid := txnMgr.getMinActiveTIDSite(sid)              *)
  (*     if tid < min {                                      *)
  (*         min = tid                                       *)
  (*     }                                                   *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_ref_to); first auto.
  iIntros (sidRef) "HsidRef".
  wp_pures.
  set P := λ (i : u64), (∃ (tidmin : u64),
    "HminRef" ∷ minRef ↦[uint64T] #tidmin ∗
    "Htidlbs" ∷ [∗ list] sid ∈ (take (int.nat i) sids_all), site_min_tid_lb γ sid (int.nat tidmin))%I.
  wp_apply (wp_forUpto P _ _ (U64 0) (U64 N_TXN_SITES) sidRef with "[] [HminRef HsidRef]"); first done.
  { clear Φ.
    iIntros (i Φ) "!> (Hloop & HsidRef & %Hbound) HΦ".
    iNamed "Hloop".
    wp_pures.
    wp_load.
    wp_apply (wp_txnMgr__getMinActiveTIDSite with "Htxnmgr"); first done.
    iIntros (tid) "Htidlb".
    wp_pures.
    wp_load.
    wp_pures.

    wp_if_destruct.
    - (* Find new min. *)
      wp_store.
      iApply "HΦ".
      iModIntro.
      iFrame.
      iExists _.
      iFrame.
      replace (int.nat (word.add _ _)) with (S (int.nat i)); last by word.
      rewrite (take_S_r _ _ i); last by apply sids_all_lookup.
      iApply big_sepL_app.
      iSplitL "Htidlbs".
      { iApply (big_sepL_impl with "Htidlbs").
        iModIntro.
        iIntros (iN sid) "Hlookup Htidlb".
        (* Weaken all previous lower bounds. *)
        iApply (site_min_tid_lb_weaken with "Htidlb").
        word.
      }
      { simpl. auto. }
    - (* Same min. *)
      iApply "HΦ".
      iModIntro.
      iFrame.
      iExists _.
      iFrame.
      replace (int.nat (word.add _ _)) with (S (int.nat i)); last by word.
      rewrite (take_S_r _ _ i); last by apply sids_all_lookup.
      iApply big_sepL_app.
      iSplitL "Htidlbs"; first done.
      simpl.
      iSplit; last done.
      (* Weaken the current lower bound. *)
      iApply (site_min_tid_lb_weaken with "Htidlb").
      word.
  }
  { iFrame.
    iExists _.
    iFrame.
    replace (int.nat 0) with 0%nat; last word.
    rewrite take_0.
    auto.
  }
  iIntros "[Hloop HsidRef]".
  iNamed "Hloop".
  wp_pures.
  
  (***********************************************************)
  (* return min                                              *)
  (***********************************************************)
  wp_load.
  by iApply "HΦ".
Qed.

(*****************************************************************)
(* func (txn *Txn) Begin()                                       *)
(*****************************************************************)
Theorem wp_txn__Begin txn γ :
  {{{ own_txn_uninit txn γ }}}
    Txn__Begin #txn
  {{{ RET #(); own_txn txn γ }}}.
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
  iIntros (tid) "[Hactive %HtidNZ]".

  (***********************************************************)
  (* txn.tid = tid                                           *)
  (***********************************************************)
  wp_pures.
  wp_storeField.
  
  (***********************************************************)
  (* txn.wrbuf.Clear()                                       *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_wrbuf__Clear with "HwrbufRP").
  iIntros "HwrbufRP".
  wp_pures.
  
  iModIntro.
  iApply "HΦ".
  iExists tid, ∅.
  eauto 15 with iFrame.
Qed.

(*****************************************************************)
(* func (txn *Txn) Get(key uint64) (uint64, bool)                *)
(*****************************************************************)
Theorem wp_txn__Get txn (k : u64) γ :
  {{{ own_txn txn γ }}}
    Txn__Get #txn #k
  {{{ (v : u64) (found : bool), RET (#v, #found); own_txn txn γ }}}.
Proof.
  iIntros (Φ) "Htxn HΦ".
  iNamed "Htxn".
  iNamed "Himpl".
  wp_call.

  (***********************************************************)
  (* wrbuf := txn.wrbuf                                      *)
  (* valb, del, found := wrbuf.Lookup(key)                   *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_wrbuf__Lookup with "HwrbufRP").
  iIntros (v d ok) "[HwrbufRP %HLookup]".
  wp_pures.

  (***********************************************************)
  (* if found {                                              *)
  (*     return valb, !del                                   *)
  (* }                                                       *)
  (***********************************************************)
  unfold spec_wrbuf__Lookup in HLookup.
  wp_if_destruct.
  { wp_pures.
    iModIntro.
    iApply "HΦ".
    eauto 15 with iFrame.
  }

  (***********************************************************)
  (* idx := txn.idx                                          *)
  (* tuple := idx.GetTuple(key)                              *)
  (* val, ret := tuple.ReadVersion(txn.tid)                  *)
  (* return val, ret == common.RET_SUCCESS                   *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_index__GetTuple with "HidxRI").
  iIntros (tuple) "#HtupleRI".
  wp_pures.
  wp_loadField.
  wp_apply (wp_tuple__ReadVersion with "HtupleRI [Hactive]").
  { unfold active_tid. eauto with iFrame. }
  iIntros (val ret latch) "[Hactive [Hlocked Hread]]".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  eauto 15 with iFrame.
Qed.

(*****************************************************************)
(* func (txn *Txn) Put(key, val uint64)                          *)
(*****************************************************************)
Theorem wp_txn__Put txn (k : u64) (v : u64) γ :
  {{{ own_txn txn γ }}}
    Txn__Put #txn #k #v
  {{{ RET #(); own_txn txn γ }}}.
Proof.
  iIntros (Φ) "Htxn HΦ".
  iNamed "Htxn".
  iNamed "Himpl".
  wp_call.
  
  (***********************************************************)
  (* wrbuf := txn.wrbuf                                      *)
  (* wrbuf.Put(key, val)                                     *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_wrbuf__Put with "HwrbufRP").
  iIntros "HwrbufRP".
  wp_pures.

  iModIntro.
  iApply "HΦ".
  eauto 15 with iFrame.
Qed.

(*****************************************************************)
(* func (txn *Txn) Delete(key uint64) bool                       *)
(*****************************************************************)
Theorem wp_txn__Delete txn (k : u64) γ :
  {{{ own_txn txn γ }}}
    Txn__Delete #txn #k
  {{{ (ok : bool), RET #ok; own_txn txn γ }}}.
Proof.
  iIntros (Φ) "Htxn HΦ".
  iNamed "Htxn".
  iNamed "Himpl".
  wp_call.
  
  (***********************************************************)
  (* wrbuf := txn.wrbuf                                      *)
  (* wrbuf.Delete(key)                                       *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_wrbuf__Delete with "HwrbufRP").
  iIntros "HwrbufRP".
  wp_pures.

  (***********************************************************)
  (* return true                                             *)
  (***********************************************************)
  iModIntro.
  iApply "HΦ".
  eauto 15 with iFrame.
Qed.

Theorem wp_txn__Commit txn γ :
  {{{ own_txn txn γ }}}
    Txn__Commit #txn
  {{{ RET #(); own_txn_uninit txn γ }}}.
Admitted.

End heap.
