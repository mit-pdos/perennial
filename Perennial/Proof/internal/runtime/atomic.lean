/-
Package initialization of `internal/runtime/atomic` (only its types are
translated, for `runtime`, which imports it).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.internal.runtime.atomic
public import Perennial.GeneratedProof.internal.runtime.atomic

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace internal.runtime.atomic

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
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
