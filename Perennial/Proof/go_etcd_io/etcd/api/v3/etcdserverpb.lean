/-
Port of `new/proof/go_etcd_io/etcd/api/v3/etcdserverpb.v`: an axiomatized (as
in Rocq) specification of marshalling `InternalRaftRequest`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Proof.go_etcd_io.etcd.api.v3.mvccpb
import Perennial.Proof.go_etcd_io.etcd.api.v3.membershippb
import Perennial.Code.go_etcd_io.etcd.api.v3.etcdserverpb
import Perennial.GeneratedProof.go_etcd_io.etcd.api.v3.etcdserverpb

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.etcd.api.v3.etcdserverpb

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : etcdserverpb.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb :=
  build_get_is_pkg_init_wf

/- FIXME (from Rocq): annoying to even state axioms about marshalling this
stuff. Want to turn the protobuf data into Gallina. -/
axiom InternalRaftRequestC : Type
axiom own_InternalRaftRequest
    (req : etcdserverpb.InternalRaftRequest.t) (req_abs : InternalRaftRequestC) : IProp GF
axiom is_RaftRequest_marshalled (req_abs : InternalRaftRequestC) (data : List w8) : Prop

axiom own_InternalRaftRequest_new_header
    (req : etcdserverpb.InternalRaftRequest.t) (hdr_ptr : loc)
    (hdr : etcdserverpb.RequestHeader.t) (req_abs : InternalRaftRequestC) :
    own_InternalRaftRequest (GF := GF) req req_abs -∗
    hdr_ptr ↦ hdr -∗
    ∃ req_abs', own_InternalRaftRequest ({ req with Header' := hdr_ptr }) req_abs'

axiom wp_InternalRaftRequest__Marshal [package_sem : etcdserverpb.Assumptions] (m_ptr : loc) (m : etcdserverpb.InternalRaftRequest.t)
    (msg : InternalRaftRequestC) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
       m_ptr ↦ m ∗ own_InternalRaftRequest m msg }}
      (App (Val (m_ptr @!! go.type.PointerType etcdserverpb.InternalRaftRequest @!! go!"Marshal"))
        (Val #()))
    {{ (dAtA_sl : slice.t) (err : error.t), RET #(dAtA_sl, err);
        m_ptr ↦ m ∗
        own_InternalRaftRequest m msg ∗
        if decide (err = interface.nil) then
          ∃ dAtA, dAtA_sl ↦*□ dAtA ∧ ⌜is_RaftRequest_marshalled msg dAtA⌝
        else
          ⌜dAtA_sl = slice.nil⌝ }}

end wps

end go_etcd_io.etcd.api.v3.etcdserverpb

end Perennial
