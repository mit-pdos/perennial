/-
Port of `new/proof/go_etcd_io/etcd/api/v3/mvccpb.v`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.go_etcd_io.etcd.api.v3.mvccpb
import Perennial.GeneratedProof.go_etcd_io.etcd.api.v3.mvccpb

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.etcd.api.v3.mvccpb

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : mvccpb.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb :=
  build_get_is_pkg_init_wf

end wps

end go_etcd_io.etcd.api.v3.mvccpb

end Perennial
