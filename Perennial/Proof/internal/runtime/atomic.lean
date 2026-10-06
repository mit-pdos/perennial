/-
Package initialization of `internal/runtime/atomic` (only its types are
translated, for `runtime`, which imports it). Not in Rocq.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.internal.runtime.atomic
import Perennial.GeneratedProof.internal.runtime.atomic

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace internal.runtime.atomic

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.runtime.atomic.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.runtime.atomic :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.runtime.atomic :=
  build_get_is_pkg_init_wf

end init

end internal.runtime.atomic

end Perennial
end
