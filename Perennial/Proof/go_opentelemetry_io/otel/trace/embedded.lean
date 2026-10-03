/-
Package initialization instances of `go.opentelemetry.io/otel/trace/embedded` (only its types are translated).
Not in Rocq.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.go_opentelemetry_io.otel.trace.embedded
import Perennial.GeneratedProof.go_opentelemetry_io.otel.trace.embedded

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace go_opentelemetry_io.otel.trace.embedded

section init
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_opentelemetry_io.otel.trace.embedded.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_opentelemetry_io.otel.trace.embedded :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_opentelemetry_io.otel.trace.embedded :=
  build_get_is_pkg_init_wf

end init

end go_opentelemetry_io.otel.trace.embedded

end Perennial
end
