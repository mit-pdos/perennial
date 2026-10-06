/-
Package initialization instances of `github.com/prometheus/client_model/go` (only its types are translated).
Not in Rocq.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.github_com.prometheus.client_model.go
import Perennial.GeneratedProof.github_com.prometheus.client_model.go

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.prometheus.client_model.go

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.prometheus.client_model.go.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.prometheus.client_model.go :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.prometheus.client_model.go :=
  build_get_is_pkg_init_wf

end init

end github_com.prometheus.client_model.go

end Perennial
end
