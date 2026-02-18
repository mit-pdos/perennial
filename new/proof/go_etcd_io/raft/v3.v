From New.code.go_etcd_io.raft Require Import v3.
Require Import New.generatedproof.go_etcd_io.raft.v3
  New.generatedproof.go_etcd_io.raft.v3.raftpb.
From New.proof.go_etcd_io.raft.v3_proof Require Export base protocol.
From New.proof Require Import grove_prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.

Definition is_Node (γ : raft_names) n : iProp Σ :=
  ∃ (n_ptr : loc),
    "%Hn" ∷ ⌜ n = interface.mk (go.PointerType raft.node) #n_ptr ⌝ ∗
    "#Hnode" ∷ is_node γ n_ptr.

Lemma wp_Node__Propose  ctx ctx_desc n γraft data_sl data :
  {{{ is_pkg_init raft ∗
      "#Hctx" ∷ is_Context ctx ctx_desc ∗
      "#Hnode" ∷ is_Node γraft n ∗
      "data_sl" ∷ data_sl ↦* data ∗
      "Hupd" ∷ (|={⊤,∅}=> ∃ log, own_raft_log γraft log ∗ (own_raft_log γraft (log ++ [data]) ={∅,⊤}=∗ True))
  }}}
    #(methods n.(interface.ty) "Propose" n.(interface.v)) #(interface.ok ctx) #data_sl
  {{{ (err : error.t), RET #err; True }}}.
Proof.
  wp_start. iNamed "Hpre". iNamed "Hnode". subst. simpl.
  wp_apply (wp_node__Propose with "[$]").
  iIntros (?) "_". by iApply "HΦ".
Qed.

End proof.
