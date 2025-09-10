Require Export New.code.go_etcd_io.etcd.api.v3.etcdserverpb.
Require Export New.generatedproof.go_etcd_io.etcd.api.v3.etcdserverpb.
Require Export New.proof.proof_prelude.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
#[global] Instance : IsPkgInit etcdserverpb := define_is_pkg_init True%I.

(* FIXME: annoying to even state axioms about marshalling this stuff.
   Want to turn the protobuf data into Gallina.
 *)
Axiom InternalRaftRequestC : Type.
Axiom own_InternalRaftRequest :
  ∀ (req : etcdserverpb.InternalRaftRequest.t) (req_abs : InternalRaftRequestC), iProp Σ.
Axiom is_RaftRequest_marshalled : ∀ (req_abs : InternalRaftRequestC) (data : list w8), Prop.

Axiom own_InternalRaftRequest_new_header :
  ∀ req hdr_ptr (hdr : etcdserverpb.RequestHeader.t) req_abs,
  own_InternalRaftRequest req req_abs -∗
  hdr_ptr ↦ hdr -∗
  ∃ req_abs',
    own_InternalRaftRequest (req <| etcdserverpb.InternalRaftRequest.Header' := hdr_ptr |>) req_abs'.

Axiom wp_InternalRaftRequest__Marshal : ∀ m_ptr m msg,
  {{{ is_pkg_init etcdserverpb ∗ m_ptr ↦ m ∗ own_InternalRaftRequest m msg }}}
    m_ptr @ (ptrT.id etcdserverpb.InternalRaftRequest.id) @ "Marshal" #()
  {{{ dAtA_sl (err : error.t), RET (#dAtA_sl, #err);
      m_ptr ↦ m ∗
      own_InternalRaftRequest m msg ∗
      if decide (err = interface.nil) then
        ∃ dAtA, dAtA_sl ↦*□ dAtA ∧ ⌜ is_RaftRequest_marshalled msg dAtA ⌝
      else
        ⌜ dAtA_sl = slice.nil ⌝
  }}}.

End wps.
