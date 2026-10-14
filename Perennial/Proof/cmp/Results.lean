/-
Results of `cmp` derived from the linked ones: the specs of `isNaN` and `Less` at
`uint64` under their old names.
-/
module

public import Perennial.Proof.cmp.Link

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : cmp.Assumptions]

/-- `isNaN` on `uint64` is `false` (`cmp.wp_isNaN`, under its old name). -/
theorem cmp.wp_isNaN_uint64 : cmp.isNaN.spec (GF := GF) (hG := hG) :=
  cmp.wp_isNaN

/-- `Less` on `uint64` is `<` on the unsigned values (`cmp.wp_Less`, under its old name). -/
theorem cmp.wp_Less_uint64 : cmp.Less.spec (GF := GF) (hG := hG) :=
  cmp.wp_Less

end results

end Perennial
