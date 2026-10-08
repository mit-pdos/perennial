/-
The `IsPkgInit` instance of `sort`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.sort
public import Perennial.GeneratedProof.sort

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace sort

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.sort :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.sort :=
  build_get_is_pkg_init_wf

end proof

end sort

end Perennial
end
