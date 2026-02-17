Require Export New.generatedproof.go_etcd_io.etcd.api.v3.etcdserverpb.
Require Export New.proof.go_etcd_io.etcd.api.v3.mvccpb.
Require Export New.proof.go_etcd_io.etcd.api.v3.membershippb.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : etcdserverpb.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) etcdserverpb := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) etcdserverpb := build_get_is_pkg_init_wf.


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
    m_ptr @! (go.PointerType etcdserverpb.InternalRaftRequest) @! "Marshal" #()
  {{{ dAtA_sl (err : error.t), RET (#dAtA_sl, #err);
      m_ptr ↦ m ∗
      own_InternalRaftRequest m msg ∗
      if decide (err = interface.nil) then
        ∃ dAtA, dAtA_sl ↦*□ dAtA ∧ ⌜ is_RaftRequest_marshalled msg dAtA ⌝
      else
        ⌜ dAtA_sl = slice.nil ⌝
  }}}.

End wps.
