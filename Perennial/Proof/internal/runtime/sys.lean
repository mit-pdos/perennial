/-
Package initialization of `internal/runtime/sys` (only its types are
translated, for `runtime`, which imports it).
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.internal.runtime.sys
import Perennial.GeneratedProof.internal.runtime.sys

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace internal.runtime.sys

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.runtime.sys.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.runtime.sys :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.runtime.sys :=
  build_get_is_pkg_init_wf

end init

end internal.runtime.sys

end Perennial
end
