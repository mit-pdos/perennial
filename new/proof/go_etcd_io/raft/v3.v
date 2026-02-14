From New.code.go_etcd_io.raft Require Import v3.
Require Import New.generatedproof.go_etcd_io.raft.v3
  New.generatedproof.go_etcd_io.raft.v3.raftpb.
From New.proof.go_etcd_io.raft.v3_proof Require Export base protocol.
From New.proof Require Import grove_prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) raft := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) raft := build_get_is_pkg_init_wf.
Definition is_Node (γ : raft_names) (n : raft.Node.t) : iProp Σ :=
  ∃ (n_ptr : loc),
    "%Hn" ∷ ⌜ n = interface.mk (ptrT.id raft.node.id) #n_ptr ⌝ ∗
    "#Hnode" ∷ is_node γ n_ptr.

Lemma wp_Node__Propose  ctx ctx_desc n γraft data_sl data :
  {{{ is_pkg_init raft ∗
      "#Hctx" ∷ is_Context ctx ctx_desc ∗
      "#Hnode" ∷ is_Node γraft n ∗
      "data_sl" ∷ data_sl ↦* data ∗
      "Hupd" ∷ (|={⊤,∅}=> ∃ log, own_raft_log γraft log ∗ (own_raft_log γraft (log ++ [data]) ={∅,⊤}=∗ True))
  }}}
    interface.get #"Propose" #n #ctx #data_sl
  {{{ (err : error.t), RET #err; True }}}.
Proof.
  wp_start. iNamed "Hpre". iNamed "Hnode". subst.
  wp_auto. wp_apply (wp_node__Propose with "[$]").
  iIntros (?) "_". by iApply "HΦ".
Qed.

End proof.
