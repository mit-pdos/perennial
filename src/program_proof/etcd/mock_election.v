From Goose.github_com.mit_pdos.gokv.etcd Require Import election .
From Perennial.program_proof Require Import grove_prelude.
From iris.base_logic Require Import ghost_map.

Class etcdG Σ := {
    etcd_mapG :> ghost_mapG Σ string string ;
}.

Module Op.
Inductive t :=
  | PutWithLease (k:string) (v:string) (l:string)
  | Get (k:string)
  | Delete (k:string)
.
End Op.

Section op_axioms.
Context `{!heapGS Σ}.
Axiom own_Op : ∀ (o:loc) (op:Op.t), iProp Σ.

Axiom wp_OpPutWithLease : ∀ key v lease,
  {{{ True }}}
    OpPutWithLease #(str key) #(str v) #(str lease)
  {{{ o, RET #o; own_Op o $ Op.PutWithLease key v lease }}}
.

Axiom wp_OpGet : ∀ key,
  {{{ True }}}
    OpGet #(str key)
  {{{ o, RET #o; own_Op o $ Op.Get key }}}
.

Axiom wp_OpDelete : ∀ key,
  {{{ True }}}
    OpDelete #(str key)
  {{{ o, RET #o; own_Op o $ Op.Delete key }}}
.
End op_axioms.

Module ResponseHeader.
Section ResponseHeader.
Record t :=
mk {
    Revision : u64;
  }.

Context `{!heapGS Σ}.
Definition own (r:loc) (x:t) : iProp Σ :=
  "HRevision" ∷ r ↦[ResponseHeader :: "Revision"] #x.(Revision)
.
End ResponseHeader.
End ResponseHeader.

Module KeyValue.
Section KeyValue.
Record t :=
mk {
    Key : string ;
    Value : string ;
    CreateRevision : u64 ;
  }.
Context `{!heapGS Σ}.

Definition own (r:loc) (x:t) : iProp Σ :=
  "HKey" ∷ r ↦[KeyValue :: "Key"] #(str x.(Key)) ∗
  "HValue" ∷ r ↦[KeyValue :: "Value"] #(str x.(Value)) ∗
  "HCreateRevision" ∷ r ↦[KeyValue :: "CreateRevision"] #x.(CreateRevision)
  .

End KeyValue.
End KeyValue.

Module RangeResponse.
Section RangeResponse.
Record t :=
mk {
    Kvs : list KeyValue.t
  }.
Context `{!heapGS Σ}.

Definition own (r:loc) (x:t) : iProp Σ :=
  ∃ kvs_ptrs kvs_sl ,
  "HKvs" ∷ r ↦[RangeResponse :: "Kvs"] (slice_val kvs_sl) ∗
  "HKvs_sl" ∷ own_slice kvs_sl ptrT 1 kvs_ptrs ∗
  "Hkvs_own" ∷ ([∗ list] p; kv ∈ kvs_ptrs ; x.(Kvs), KeyValue.own p kv)
.

End RangeResponse.
End RangeResponse.

Module TxnResponse.
Section TxnResponse.
Record t :=
mk {
    Succeeded : bool ;
    Header : ResponseHeader.t ;
    Responses : list RangeResponse.t
  }.

Context `{!heapGS Σ}.
Definition own (r:loc) (x:t) : iProp Σ :=
  ∃ (rh:loc) resps_sl (resps : list loc),
  "HSucceeded" ∷ r ↦[TxnResponse :: "Succeeded"] #x.(Succeeded) ∗
  "HHeader" ∷ r ↦[TxnResponse :: "Header"] #rh ∗
  "HHeader_own" ∷ ResponseHeader.own rh x.(Header) ∗
  "HResponses" ∷ r ↦[TxnResponse :: "Responses"] (slice_val resps_sl) ∗
  "HResp_sl" ∷ own_slice_small resps_sl ptrT 1 resps ∗
  "Hresps_own" ∷ ([∗ list] resp_ptr; resp ∈ resps; x.(Responses),
      RangeResponse.own resp_ptr resp)
.

End TxnResponse.
End TxnResponse.

Section txn_axioms.
Context `{!etcdG Σ}.
Context `{!heapGS Σ}.

Axiom own_Txn : ∀ (t:loc) (cmp:option (string * u64)) (thenOps elseOps : list Op.t), iProp Σ.

Axiom wp_StartTxn :
  {{{ True }}}
    StartTxn #()
  {{{ t, RET #t; own_Txn t None [] [] }}}
.

Axiom wp_Txn__Then : ∀ t o op cmp thenOps elseOps,
  {{{ own_Txn t cmp thenOps elseOps ∗ own_Op o op }}}
    Txn__Then #t #o
  {{{ t, RET #t; own_Txn t cmp (thenOps ++ [op]) elseOps }}}
.

Axiom wp_Txn__Else : ∀ t o op cmp thenOps elseOps,
  {{{ own_Txn t cmp thenOps elseOps ∗ own_Op o op }}}
    Txn__Else #t #o
  {{{ t, RET #t; own_Txn t cmp thenOps (elseOps ++ [op]) }}}
.

Axiom wp_Txn__IfCreateRevisionEq : ∀ t k ver,
  {{{ own_Txn t None [] [] }}}
    Txn__IfCreateRevisionEq #t #(str k) #ver
  {{{ t, RET #t; own_Txn t (Some (k, ver)) [] [] }}}
.

Axiom wp_Txn__Commit : ∀ t cmp thenOps elseOps,
  {{{ own_Txn t (Some cmp) thenOps elseOps }}}
    Txn__Commit #t
  {{{ r_ptr r (err:u64), RET (#r_ptr, #err); TxnResponse.own r_ptr r }}}
.

Local Definition keys (ops:list Op.t) : gset string.
Admitted.

Definition op_update γ op Φ : iProp Σ :=
  match op with
  | Op.Get k =>
      ∃ v, k ↪[γ] v ∗ (k ↪[γ] v -∗ Φ (RangeResponse.mk [KeyValue.mk k v 37])) (* TODO: track CreateRev *)
  | Op.PutWithLease k v l =>
   (* TODO: lease *)
      ∃ oldv, k ↪[γ] oldv ∗ (k ↪[γ] v -∗ Φ (RangeResponse.mk []))
  | Op.Delete k => (* TODO: deletion seems to be indicated by CreateRev = 0.
                       https://github.com/etcd-io/etcd/issues/6740 *)
      False
end
.

(* Atomic update for committing a transaction *)
Definition txn_atomic_update γ (cmp:string * u64) (thenOps elseOps : list Op.t)
           (Φ: list RangeResponse.t → iProp Σ)
  : iProp Σ :=
  |={⊤,∅}=>
  ∃ v,
  cmp.1 ↪[γ] v ∗
  (cmp.1 ↪[γ] v -∗
   if (decide (cmp.2 = cmp.2)) then (* TODO: need model for etcd's versioned kv state *)
     (* "then" case *)
     (fold_right
        (λ op Φcont, (λ prevResponses, op_update γ op (λ resp, Φcont (prevResponses ++ [resp]))))
        (λ x, |={∅,⊤}=> Φ x)%I
        thenOps)
       []
   else
     (* "else" case *)
     (fold_right
        (λ op Φcont, (λ prevResponses, op_update γ op (λ resp, Φcont (prevResponses ++ [resp]))))
        (λ x, |={∅,⊤}=> Φ x)%I
        elseOps)
       []
  )
.

Lemma test_txn_atomic_update γ Φ :
  "Ha" ∷ "a" ↪[γ] "aold" ∗
  "Hx" ∷ "x" ↪[γ] "y" ∗
  "Hc" ∷ "c" ↪[γ] "cold" -∗
  txn_atomic_update γ ("x",U64 0)
                    [Op.Get "x" ; Op.PutWithLease "a" "b" "x"; Op.PutWithLease "c" "d" "x"]
                    [] Φ.
Proof.
  rewrite /txn_atomic_update /=.
  iNamed 1.
  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iExists _; iFrame.
  setoid_rewrite decide_True; last word.
  iIntros "Hx".
  iExists _; iFrame.
  iIntros "Hx".
  iExists _; iFrame.
  iIntros "Ha".
  iExists _; iFrame.
  iIntros "Hc".
  iMod "Hmask" as "_".
Admitted.

End txn_axioms.

Section proof.

Context `{!etcdG Σ}.
Context `{!heapGS Σ}.

Definition own_Election (e:loc) : iProp Σ :=
  ∃ (lease keyPrefix leaderLease leaderKey: string) (leaderRev:u64),
  "Hlease" ∷ e ↦[Election :: "lease"] #(str lease) ∗
  "HkeyPrefix" ∷ e ↦[Election :: "keyPrefix"] #(str keyPrefix) ∗
  "HleaderLease" ∷ e ↦[Election :: "leaderLease"] #(str leaderLease) ∗
  "HleaderKey" ∷ e ↦[Election :: "leaderKey"] #(str leaderKey) ∗
  "HleaderRev" ∷ e ↦[Election :: "leaderRev"] #leaderRev
.

Axiom wp_waitDeletes : ∀ pfx (rev:u64),
  {{{ True }}}
    waitDeletes #(str pfx) #rev
  {{{ (err:u64), RET #err; True }}}.

Lemma wp_Campaign e (v:string) :
  {{{
        "Hown" ∷ own_Election e
  }}}
    Election__Campaign #e #(str v)
  {{{
        (err:u64), RET #err; True
  }}}
.
Proof.
  iIntros (?) "H HΦ". iNamed "H".
  iNamed "Hown".
  wp_rec.
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_apply wp_StartTxn.
  iIntros (?) "Htxn".
  wp_apply (wp_Txn__IfCreateRevisionEq with "[$]").
  iIntros (?) "Htxn".
  wp_apply wp_ref_to.
  { val_ty. }
  iIntros (txn_ptr) "Htxn_ptr".
  wp_pures.
  wp_loadField.
  wp_apply wp_OpPutWithLease.
  iIntros (?) "Hop".
  wp_load.
  wp_apply (wp_Txn__Then with "[$]").
  iIntros (?) "Htxn".
  wp_store.
  wp_apply wp_OpGet.
  iIntros (?) "Hop".
  wp_load.
  wp_apply (wp_Txn__Else with "[$]").
  iIntros (?) "Htxn".
  wp_store.

  wp_apply wp_ref_of_zero; first done.
  iIntros (resp_ptr) "Hresp_ptr".
  wp_pures.
  wp_apply wp_ref_of_zero; first done.
  iIntros (err_ptr) "Herr".
  wp_pures.
  wp_load.
  wp_apply (wp_Txn__Commit with "[$]").
  iIntros (???) "Hresp".
  wp_pures.
  wp_store.
  wp_store.
  wp_load.
  wp_if_destruct.
  {
    wp_load.
    by iApply "HΦ".
  }
  wp_storeField.
  wp_load.
  iNamed "Hresp".
  wp_loadField.
  wp_loadField.
  wp_storeField.
  wp_storeField.
  wp_apply wp_ref_to; first val_ty.
  iIntros (?) "Hdone".
  wp_pures.
  wp_load. wp_loadField.
  wp_if_destruct.
  { (* case: txn "else" *)
    wp_load.
    wp_loadField.
    admit. (* TODO: need to know that if commit `Succeeded`, then there are actually responses *)
  }
  (* case: txn "then" *)
  wp_pures.
  wp_load.
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_apply wp_waitDeletes.
  iIntros (?) "_".
  wp_store.
  wp_load.
  wp_if_destruct.
  { wp_pures. by iApply "HΦ". }
  { wp_pures. by iApply "HΦ". }
Admitted.

End proof.
