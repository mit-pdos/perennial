From Perennial.program_proof.mvcc Require Import txn_prelude.
From Perennial.program_proof.mvcc Require Import txnmgr_repr tuple_repr index_proof wrbuf_proof.

Section repr.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

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
Definition own_txn (txn : loc) (ts : nat) (view : dbmap) γ τ : iProp Σ :=
  ∃ (mods : dbmap),
    "Himpl"    ∷ own_txn_impl txn ts mods γ ∗
    "#Hltuples" ∷ ([∗ map] k ↦ v ∈ view, ltuple_ptsto γ k v ts) ∗
    "Htxnmap"  ∷ txnmap_auth τ (mods ∪ view) ∗
    "%Hmodsdom" ∷ ⌜dom mods ⊆ dom view⌝.

Definition own_tuples_locked (ts : nat) (mods : dbmap) γ : iProp Σ :=
  [∗ map] k ↦ _ ∈ mods, ∃ tuple phys, own_tuple_locked tuple k ts phys phys γ.

Definition own_tuples_updated (ts : nat) (mods : dbmap) γ : iProp Σ :=
  [∗ map] k ↦ v ∈ mods, ∃ tuple phys,
      own_tuple_locked tuple k ts phys (extend (S ts) phys ++ [v]) γ.

Definition own_txn_ready (txn : loc) (ts : nat) (view : dbmap) γ τ : iProp Σ :=
  ∃ (mods : dbmap),
    "Himpl"     ∷ own_txn_impl txn ts mods γ ∗
    "#Hltuples" ∷ ([∗ map] k ↦ v ∈ view, ltuple_ptsto γ k v ts) ∗
    "Htxnmap"   ∷ txnmap_auth τ (mods ∪ view) ∗
    "%Hmodsdom" ∷ ⌜dom mods ⊆ dom view⌝ ∗
    (* FIXME: make [tuple] below a physical thing. *)
    "Htuples"   ∷ own_tuples_locked ts mods γ.

Definition own_txn_appliable (txn : loc) (ts : nat) (view : dbmap) γ τ : iProp Σ :=
  ∃ (mods : dbmap),
    "Himpl"     ∷ own_txn_impl txn ts mods γ ∗
    "#Hltuples" ∷ ([∗ map] k ↦ v ∈ view, ltuple_ptsto γ k v ts) ∗
    "Htxnmap"   ∷ txnmap_auth τ (mods ∪ view) ∗
    "%Hmodsdom" ∷ ⌜dom mods ⊆ dom view⌝ ∗
    (* FIXME: make [tuple] below a physical thing. *)
    "Htuples"   ∷ own_tuples_updated ts mods γ.

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

Lemma own_txn_impl_tid txn ts m γ :
  own_txn_impl txn ts m γ -∗
  ∃ (tid : u64), ⌜int.nat tid = ts⌝.
Proof. iIntros "Htxn". iNamed "Htxn". eauto. Qed.

End lemma.
