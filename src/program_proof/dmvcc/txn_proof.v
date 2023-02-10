From Perennial.program_proof.mvcc Require Export
     mvcc_prelude mvcc_action mvcc_ghost mvcc_inv.
From Perennial.program_proof.mvcc Require Import
     txnmgr_repr tuple_repr index_proof wrbuf_repr.
From Goose.github_com.mit_pdos.gokv.dmvcc Require Export txn.

Section repr.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Instance string_IntoVal : IntoVal string.
Proof.
  refine {| to_val := λ (s:string), #(LitString s);
           from_val := λ v, match v with #(LitString s) => Some s | _ => None end;
             IntoVal_def := "";
    |}; done.
Qed.

Definition own_txn_clerk_impl (txn : loc) (mods: dbmap) (ts : nat) γ : iProp Σ :=
  ∃ (tid : u64) (indexCk txnmgrHost : loc) (p : proph_id) (writes_loc:loc) (writes:gmap u64 string),
    "Htid" ∷ txn ↦[txn.Clerk :: "tid"] #tid ∗
    "%Htid" ∷ ⌜int.nat tid = ts⌝ ∗
    "Hwrites" ∷ txn ↦[txn.Clerk :: "writes"] #writes_loc ∗
    "HwritesM" ∷ is_map writes_loc 1 writes ∗
    "%HwritesMods" ∷ ⌜mods = fmap (λ v, Some v) writes⌝ ∗
    "#Hidx" ∷ readonly (txn ↦[txn.Clerk :: "indexCk"] #indexCk) ∗
    "#Htxnmgr" ∷ readonly (txn ↦[txn.Clerk :: "txnMgrHost"] #txnmgrHost) ∗
    (* FIXME: will want clerk verions of these
    "#HidxRI" ∷ is_index idx γ ∗
    "#HtxnmgrRI" ∷ is_txnmgr txnmgr γ ∗
     *)
    "#Hp" ∷ readonly (txn ↦[txn.Clerk :: "p"] #p) ∗
    "#Hinv" ∷ mvcc_inv_sst γ p ∗
    "_" ∷ True.

(* TODO: Unify [own_txn_clerk] and [own_txn_clerk_ready]. *)
Definition own_txn_clerk (txn : loc) (ts : nat) (view : dbmap) γ τ : iProp Σ :=
  ∃ (mods : dbmap),
    "Himpl"     ∷ own_txn_clerk_impl txn mods ts γ ∗
    "#Hltuples" ∷ ([∗ map] k ↦ v ∈ view, ltuple_ptsto γ k v ts) ∗
    "Htxnmap"   ∷ txnmap_auth τ (mods ∪ view) ∗
    "%Hmodsdom" ∷ ⌜dom mods ⊆ dom view⌝
.

Definition own_txn_clerk_ready (txn : loc) (ts : nat) (view : dbmap) γ τ : iProp Σ :=
  ∃ (mods : dbmap) (tpls : gmap u64 loc),
    "Himpl"     ∷ own_txn_clerk_impl txn mods ts γ ∗
    "#Hltuples" ∷ ([∗ map] k ↦ v ∈ view, ltuple_ptsto γ k v ts) ∗
    "Htxnmap"   ∷ txnmap_auth τ (mods ∪ view) ∗
    "%Hmodsdom" ∷ ⌜dom mods ⊆ dom view⌝ ∗
    "Htuples"   ∷ own_tuples_locked ts tpls γ.

(* TODO: Unify [own_txn_impl] and [own_txn_uninit]. *)
Definition own_txn_clerk_uninit (txn : loc) γ : iProp Σ :=
  ∃ (tid : u64) (indexCk txnmgrCk : loc) (p : proph_id) (writes_loc:loc) (writesM:gmap u64 string),
    "Htid" ∷ txn ↦[txn.Clerk :: "tid"] #tid ∗
    "Hwrites" ∷ txn ↦[txn.Clerk :: "writes"] #writes_loc ∗
    "HwritesM" ∷ is_map writes_loc 1 writesM ∗
    "#Hidx" ∷ readonly (txn ↦[txn.Clerk :: "indexCk"] #indexCk) ∗
    "#Htxnmgr" ∷ readonly (txn ↦[txn.Clerk :: "txnMgrHost"] #txnmgrCk) ∗
    (* FIXME: will want clerk verions of these
    "#HidxRI" ∷ is_index idx γ ∗
    "#HtxnmgrRI" ∷ is_txnmgr txnmgr γ ∗
     *)
    "#Hp" ∷ readonly (txn ↦[txn.Clerk :: "p"] #p) ∗
    "#Hinv" ∷ mvcc_inv_sst γ p ∗
    "_" ∷ True.

End repr.

#[global]
Hint Extern 1 (environments.envs_entails _ (own_txn_clerk_impl _ _ _ _)) => unfold own_txn_clerk_impl : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (own_txn_clerk _ _ _ _ _)) => unfold own_txn_clerk : core.
#[global]
Hint Extern 1 (environments.envs_entails _ (own_txn_clerk_ready _ _ _ _ _)) => unfold own_txn_clerk_ready : core.

Section lemma.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Lemma own_txn_clerk_txnmap_ptsto_dom {txn ts view k v γ τ} :
  own_txn_clerk txn ts view γ τ -∗
  txnmap_ptsto τ k v -∗
  ⌜k ∈ dom view⌝.
Proof.
  iIntros "Htxn Hptsto".
  iNamed "Htxn".
  iDestruct (txnmap_lookup with "Htxnmap Hptsto") as "%Hlookup".
  iPureIntro.
  apply elem_of_dom_2 in Hlookup. set_solver.
Qed.

Lemma own_txn_clerk_impl_tid txn wrbuf ts γ :
  own_txn_clerk_impl txn wrbuf ts γ -∗
  ∃ (tid : u64), ⌜int.nat tid = ts⌝.
Proof. iIntros "Htxn". iNamed "Htxn". eauto. Qed.

End lemma.
