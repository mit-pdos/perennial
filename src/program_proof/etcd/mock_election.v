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

Lemma wp_Campaign e (v:string) :
  {{{
        "Hown" ∷ own_Election e
  }}}
    Election__Campaign #e #(str v)
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (?) "H HΦ". iNamed "H".
  iNamed "Hown".
  wp_lam.
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
  iIntros (resp_ptr) "Hresp".
  wp_pures.
  wp_apply wp_ref_of_zero; first done.
  iIntros (err_ptr) "Herr".
  wp_pures.
  wp_load.
Admitted.

End proof.
