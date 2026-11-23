/-
Shared definitions of the proofs of the Go `internal/byteorder` package: its `isPkgInit` (the
package has no variables).
-/
module

public import Perennial.Proof.encoding.binary.Base
public import Perennial.Code.internal.byteorder
public import Perennial.GeneratedProof.internal.byteorder

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace internal.byteorder

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.byteorder.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.byteorder :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.byteorder :=
  build_get_is_pkg_init_wf

end defs

end internal.byteorder

end Perennial
