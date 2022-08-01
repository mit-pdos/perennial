(* Import definitions/theorems of the Perennial framework with the disk FFI. *)
From Perennial.program_proof Require Export grove_prelude.
(* Import Coq model of our Goose program. *)
From Goose.github_com.mit_pdos.go_mvcc Require Export txn.
From Perennial.program_proof.mvcc Require Export mvcc_ghost mvcc_misc gc_proof index_proof tuple_proof wrbuf_proof.
(* prefer untyped slices *)
Export Perennial.goose_lang.lib.slice.slice.

Section def.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(* TODO: [site_active_tids_half_auth γ sid (gset_to_gmap () (list_to_set tidsactiveL))] to remove [tidsactiveM] *)
Definition own_txnsite (txnsite : loc) (sid : u64) γ : iProp Σ := 
  (* FIXME: don't need [tidlast] anymore. *)
  ∃ (tidlast tidmin : u64) (tidsactive : Slice.t)
    (tidsactiveL : list u64) (tidsactiveM : gmap u64 unit),
    "Htidlast" ∷ txnsite ↦[TxnSite :: "tidLast"] #tidlast ∗
    "#Htslb" ∷ ts_lb γ (S (int.nat tidlast)) ∗
    "Hactive" ∷ txnsite ↦[TxnSite :: "tidsActive"] (to_val tidsactive) ∗
    "HactiveL" ∷ typed_slice.is_slice tidsactive uint64T 1 tidsactiveL ∗
    "HactiveAuth" ∷ site_active_tids_half_auth γ sid tidsactiveM ∗
    "%HactiveLM" ∷ ⌜(list_to_set tidsactiveL) = dom tidsactiveM⌝ ∗
    "%HactiveND" ∷ (⌜NoDup tidsactiveL⌝) ∗
    "HminAuth" ∷ site_min_tid_half_auth γ sid (int.nat tidmin) ∗
    "%HtidOrder" ∷ (⌜Forall (λ tid, int.Z tidmin ≤ int.Z tid ≤ int.Z tidlast) (tidlast :: tidsactiveL)⌝) ∗
    "%HtidFree" ∷ (∀ tid, ⌜int.Z tidlast < int.Z tid -> tid ∉ dom tidsactiveM⌝) ∗
    "_" ∷ True.

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

Definition is_txnmgr (txnmgr : loc) γ : iProp Σ := 
  ∃ (latch : loc) (sites : Slice.t) (idx gc : loc)
    (sitesL : list loc) (p : proph_id),
    "#Hlatch" ∷ readonly (txnmgr ↦[TxnMgr :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (own_txnmgr txnmgr) ∗
    "#Hidx" ∷ readonly (txnmgr ↦[TxnMgr :: "idx"] #idx) ∗
    "#HidxRI" ∷ is_index idx γ ∗
    "#Hgc" ∷ readonly (txnmgr ↦[TxnMgr :: "gc"] #gc) ∗
    "#Hsites" ∷ readonly (txnmgr ↦[TxnMgr :: "sites"] (to_val sites)) ∗
    "#HsitesS" ∷ readonly (is_slice_small sites ptrT 1 (to_val <$> sitesL)) ∗
    "%HsitesLen" ∷ ⌜Z.of_nat (length sitesL) = N_TXN_SITES⌝ ∗
    "#HsitesRP" ∷ ([∗ list] sid ↦ site ∈ sitesL, is_txnsite site sid γ) ∗
    "#Hp" ∷ readonly (txnmgr ↦[TxnMgr :: "p"] #p) ∗
    "#Hinvgc" ∷ mvcc_inv_gc γ ∗
    "#Hinvsst" ∷ mvcc_inv_sst γ p ∗
    "_" ∷ True.

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

Definition own_txn_impl (txn : loc) (ts : nat) (mods : dbmap) γ : iProp Σ :=
  ∃ (tid sid : u64) (wrbuf : loc) (idx txnmgr : loc) (p : proph_id),
    "Htid" ∷ txn ↦[Txn :: "tid"] #tid ∗
    (* This ensures we do not lose the info that [tid] does not overflow. *)
    "%Etid" ∷ ⌜int.nat tid = ts⌝ ∗
    "Hsid" ∷ txn ↦[Txn :: "sid"] #sid ∗
    "%HsidB" ∷ ⌜(int.Z sid) < N_TXN_SITES⌝ ∗
    "Hwrbuf" ∷ txn ↦[Txn :: "wrbuf"] #wrbuf ∗
    "HwrbufRP" ∷ own_wrbuf wrbuf mods ∗
    "#Hidx" ∷ readonly (txn ↦[Txn :: "idx"] #idx) ∗
    "#HidxRI" ∷ is_index idx γ ∗
    "#Htxnmgr" ∷ readonly (txn ↦[Txn :: "txnMgr"] #txnmgr) ∗
    "#HtxnmgrRI" ∷ is_txnmgr txnmgr γ ∗
    "Hactive" ∷ active_tid γ tid sid ∗
    "#Hp" ∷ readonly (txnmgr ↦[TxnMgr :: "p"] #p) ∗
    "#Hinv" ∷ mvcc_inv_sst γ p ∗
    "_" ∷ True.

(* TODO: Unify [own_txn] and [own_txn_ready]. *)
Definition own_txn (txn : loc) (ts : nat) γ τ : iProp Σ :=
  ∃ (view : dbmap) (mods : dbmap),
    "Himpl"    ∷ own_txn_impl txn ts mods γ ∗
    "Hltuples" ∷ ([∗ map] k ↦ v ∈ view, ltuple_ptsto γ k v ts) ∗
    "Htxnmap"  ∷ txnmap_auth τ (mods ∪ view).

Definition own_txn_ready (txn : loc) (ts : nat) γ τ : iProp Σ :=
  ∃ (view : dbmap) (mods : dbmap),
    "Himpl"    ∷ own_txn_impl txn ts mods γ ∗
    "Hltuples" ∷ ([∗ map] k ↦ v ∈ view, ltuple_ptsto γ k v ts) ∗
    "Htxnmap"  ∷ txnmap_auth τ (mods ∪ view) ∗
    "Hlocks"   ∷ ([∗ map] k ↦ _ ∈ mods, mods_token γ k ts).

Definition tuple_applied
           (tuple : loc) (tid : nat) (k : u64) (v : dbval) γ
  : iProp Σ :=
  match v with
  | Some w => tuple_appended tuple tid k w γ
  | Nil => tuple_killed tuple tid k γ
  end.

Definition own_txn_applied (txn : loc) (ts : nat) γ τ : iProp Σ :=
  ∃ (view : dbmap) (mods : dbmap),
    "Himpl"    ∷ own_txn_impl txn ts mods γ ∗
    "Hltuples" ∷ ([∗ map] k ↦ v ∈ view, ltuple_ptsto γ k v ts) ∗
    "Htxnmap"  ∷ txnmap_auth τ (mods ∪ view) ∗
    "Hlocks"   ∷ ([∗ map] k ↦ _ ∈ mods, mods_token γ k ts) ∗
    "Hphys"    ∷ ([∗ map] k ↦ v ∈ mods,
                    ∃ tuple latch, tuple_applied tuple ts k v γ ∗
                                   tuple_locked tuple k latch γ).

(* TODO: Unify [own_txn_impl] and [own_txn_uninit]. *)
Definition own_txn_uninit (txn : loc) γ : iProp Σ := 
  ∃ (tid sid : u64) (wrbuf : loc) (idx txnmgr : loc) (p : proph_id) (mods : dbmap),
    "Htid" ∷ txn ↦[Txn :: "tid"] #tid ∗
    "Hsid" ∷ txn ↦[Txn :: "sid"] #sid ∗
    "%HsidB" ∷ ⌜(int.Z sid) < N_TXN_SITES⌝ ∗
    "Hwrbuf" ∷ txn ↦[Txn :: "wrbuf"] #wrbuf ∗
    "HwrbufRP" ∷ own_wrbuf wrbuf mods ∗
    "#Hidx" ∷ readonly (txn ↦[Txn :: "idx"] #idx) ∗
    "#HidxRI" ∷ is_index idx γ ∗
    "#Htxnmgr" ∷ readonly (txn ↦[Txn :: "txnMgr"] #txnmgr) ∗
    "#HtxnmgrRI" ∷ is_txnmgr txnmgr γ ∗
    "#Hp" ∷ readonly (txnmgr ↦[TxnMgr :: "p"] #p) ∗
    "#Hinv" ∷ mvcc_inv_sst γ p ∗
    "_" ∷ True.

End def.

Hint Extern 1 (environments.envs_entails _ (own_txnsite _ _ _)) => unfold own_txnsite : core.
Hint Extern 1 (environments.envs_entails _ (own_txnmgr _)) => unfold own_txnmgr : core.
Hint Extern 1 (environments.envs_entails _ (is_txnmgr _ _)) => unfold is_txnmgr : core.
Hint Extern 1 (environments.envs_entails _ (own_txn_impl _ _ _ _)) => unfold own_txn_impl : core.
Hint Extern 1 (environments.envs_entails _ (own_txn _ _ _ _)) => unfold own_txn : core.
Hint Extern 1 (environments.envs_entails _ (own_txn_ready _ _ _ _)) => unfold own_txn_ready : core.
Hint Extern 1 (environments.envs_entails _ (own_txn_applied _ _ _ _)) => unfold own_txn_applied : core.
Hint Extern 1 (environments.envs_entails _ (own_txn_uninit _ _)) => unfold own_txn_uninit : core.

Section lemma.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Lemma own_txn_impl_tid txn ts m γ :
  own_txn_impl txn ts m γ -∗
  ∃ (tid : u64), ⌜int.nat tid = ts⌝.
Proof. iIntros "Htxn". iNamed "Htxn". eauto. Qed.

End lemma.
