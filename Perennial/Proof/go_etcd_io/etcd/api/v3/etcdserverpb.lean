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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : etcdserverpb.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb :=
  build_get_is_pkg_init_wf

/- FIXME (from Rocq): annoying to even state axioms about marshalling this
stuff. Want to turn the protobuf data into Gallina. -/
axiom InternalRaftRequestC : Type
axiom ownInternalRaftRequest
    (req : etcdserverpb.InternalRaftRequest.t) (req_abs : InternalRaftRequestC) : IProp GF
axiom IsRaftRequestMarshalled (req_abs : InternalRaftRequestC) (data : List w8) : Prop

axiom ownInternalRaftRequest_new_header
    (req : etcdserverpb.InternalRaftRequest.t) (hdr_ptr : Loc)
    (hdr : etcdserverpb.RequestHeader.t) (req_abs : InternalRaftRequestC) :
    ownInternalRaftRequest (GF := GF) req req_abs -∗
    hdr_ptr ↦ hdr -∗
    ∃ req_abs', ownInternalRaftRequest ({ req with Header' := hdr_ptr }) req_abs'

axiom InternalRaftRequest.wp_Marshal [package_sem : etcdserverpb.Assumptions] (m_ptr : Loc) (m : etcdserverpb.InternalRaftRequest.t)
    (msg : InternalRaftRequestC) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
       m_ptr ↦ m ∗ ownInternalRaftRequest m msg }}
      (App (Val (m_ptr @!! go.GoType.PointerType etcdserverpb.InternalRaftRequest @!! go!"Marshal"))
        (Val #()))
    {{ (dAtA_sl : slice.t) (err : error.t), RET #(dAtA_sl, err);
        m_ptr ↦ m ∗
        ownInternalRaftRequest m msg ∗
        if decide (err = interface.nil) then
          ∃ dAtA, dAtA_sl ↦*□ dAtA ∧ ⌜IsRaftRequestMarshalled msg dAtA⌝
        else
          ⌜dAtA_sl = slice.nil⌝ }}

end wps

end go_etcd_io.etcd.api.v3.etcdserverpb

end Perennial
