/-
Port of `new/proof/sort_proof/sort_init.v`: the `IsPkgInit` instance of `sort`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.sort
import Perennial.GeneratedProof.sort

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace sort

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
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
