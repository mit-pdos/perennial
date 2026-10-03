/-
Package initialization instances of `go.etcd.io/etcd/api/v3/authpb` (only its types are translated).
Not in Rocq.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.go_etcd_io.etcd.api.v3.authpb
import Perennial.GeneratedProof.go_etcd_io.etcd.api.v3.authpb

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace go_etcd_io.etcd.api.v3.authpb

section init
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.api.v3.authpb.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.authpb :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.authpb :=
  build_get_is_pkg_init_wf

end init

end go_etcd_io.etcd.api.v3.authpb

end Perennial
end
