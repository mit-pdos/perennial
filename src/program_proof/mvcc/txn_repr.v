From Perennial.program_proof.mvcc Require Import
     txn_prelude
     txnmgr_repr tuple_repr index_proof wrbuf_repr.

Section repr.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition own_txn_impl (txn : loc) (wrbuf : loc) (ts : nat) γ : iProp Σ :=
  ∃ (tid sid : u64) (idx txnmgr : loc) (p : proph_id),
    "Htid" ∷ txn ↦[Txn :: "tid"] #tid ∗
    (* This ensures we do not lose the info that [tid] does not overflow. *)
    "%Etid" ∷ ⌜int.nat tid = ts⌝ ∗
    "Hsid" ∷ txn ↦[Txn :: "sid"] #sid ∗
    "%HsidB" ∷ ⌜(int.Z sid) < N_TXN_SITES⌝ ∗
    "Hwrbuf"    ∷ txn ↦[Txn :: "wrbuf"] #wrbuf ∗
    "#Hidx" ∷ readonly (txn ↦[Txn :: "idx"] #idx) ∗
    "#HidxRI" ∷ is_index idx γ ∗
    "#Htxnmgr" ∷ readonly (txn ↦[Txn :: "txnMgr"] #txnmgr) ∗
    "#HtxnmgrRI" ∷ is_txnmgr txnmgr γ ∗
    "Hactive" ∷ active_tid γ tid sid ∗
    "#Hp" ∷ readonly (txnmgr ↦[TxnMgr :: "p"] #p) ∗
    "#Hinv" ∷ mvcc_inv_sst γ p ∗
    "_" ∷ True.

(* TODO: Unify [own_txn] and [own_txn_ready]. *)
Definition own_txn (txn : loc) (ts : nat) (view : dbmap) γ τ : iProp Σ :=
  ∃ (wrbuf : loc) (mods : dbmap),
    "Himpl"     ∷ own_txn_impl txn wrbuf ts γ ∗
    "#Hltuples" ∷ ([∗ map] k ↦ v ∈ view, ltuple_ptsto γ k v ts) ∗
    "Htxnmap"   ∷ txnmap_auth τ (mods ∪ view) ∗
    "%Hmodsdom" ∷ ⌜dom mods ⊆ dom view⌝ ∗
    "HwrbufRP"  ∷ own_wrbuf_xtpls wrbuf mods.

Definition own_txn_ready (txn : loc) (ts : nat) (view : dbmap) γ τ : iProp Σ :=
  ∃ (wrbuf : loc) (mods : dbmap) (tpls : gmap u64 loc),
    "Himpl"     ∷ own_txn_impl txn wrbuf ts γ ∗
    "#Hltuples" ∷ ([∗ map] k ↦ v ∈ view, ltuple_ptsto γ k v ts) ∗
    "Htxnmap"   ∷ txnmap_auth τ (mods ∪ view) ∗
    "%Hmodsdom" ∷ ⌜dom mods ⊆ dom view⌝ ∗
    "HwrbufRP"  ∷ own_wrbuf wrbuf mods tpls ∗
    "Htuples"   ∷ own_tuples_locked ts tpls γ.

(* TODO: Unify [own_txn_impl] and [own_txn_uninit]. *)
Definition own_txn_uninit (txn : loc) γ : iProp Σ := 
  ∃ (tid sid : u64) (wrbuf : loc) (idx txnmgr : loc) (p : proph_id) (mods : dbmap),
    "Htid" ∷ txn ↦[Txn :: "tid"] #tid ∗
    "Hsid" ∷ txn ↦[Txn :: "sid"] #sid ∗
    "%HsidB" ∷ ⌜(int.Z sid) < N_TXN_SITES⌝ ∗
    "Hwrbuf" ∷ txn ↦[Txn :: "wrbuf"] #wrbuf ∗
    "HwrbufRP" ∷ own_wrbuf_xtpls wrbuf mods ∗
    "#Hidx" ∷ readonly (txn ↦[Txn :: "idx"] #idx) ∗
    "#HidxRI" ∷ is_index idx γ ∗
    "#Htxnmgr" ∷ readonly (txn ↦[Txn :: "txnMgr"] #txnmgr) ∗
    "#HtxnmgrRI" ∷ is_txnmgr txnmgr γ ∗
    "#Hp" ∷ readonly (txnmgr ↦[TxnMgr :: "p"] #p) ∗
    "#Hinv" ∷ mvcc_inv_sst γ p ∗
    "_" ∷ True.

End repr.

#[global]
Hint Extern 1 (environments.envs_entails _ (own_txn_impl _ _ _ _)) => unfold own_txn_impl : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (own_txn _ _ _ _ _)) => unfold own_txn : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (own_txn_ready _ _ _ _ _)) => unfold own_txn_ready : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (own_txn_uninit _ _)) => unfold own_txn_uninit : core.

Section lemma.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Lemma own_txn_txnmap_ptsto_dom {txn ts view k v γ τ} :
  own_txn txn ts view γ τ -∗
  txnmap_ptsto τ k v -∗
  ⌜k ∈ dom view⌝.
Proof.
  iIntros "Htxn Hptsto".
  iNamed "Htxn".
  iDestruct (txnmap_lookup with "Htxnmap Hptsto") as "%Hlookup".
  iPureIntro.
  apply elem_of_dom_2 in Hlookup. set_solver.
Qed.

Lemma own_txn_impl_tid txn wrbuf ts γ :
  own_txn_impl txn wrbuf ts γ -∗
  ∃ (tid : u64), ⌜int.nat tid = ts⌝.
Proof. iIntros "Htxn". iNamed "Htxn". eauto. Qed.

End lemma.
