/-
Results of `math/bits` derived from the linked ones: `wp_Len64_exact` and `wp_Len_exact`, the
old names of the specs of `Len64` and `Len`.
-/
module

public import Perennial.Proof.math.bits.Link

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

/-- `math.bits.Len64(x)` is the bit length of `x`. (`Len64`'s one spec, `math.bits.wp_Len64`,
under its old name.) -/
theorem math.bits.wp_Len64_exact : math.bits.Len64.spec (GF := GF) (hG := hG) :=
  math.bits.wp_Len64

/-- `math.bits.Len(x)` is the bit length of `x`. (`Len`'s one spec, `math.bits.wp_Len`, under
its old name.) -/
theorem math.bits.wp_Len_exact : math.bits.Len.spec (GF := GF) (hG := hG) :=
  math.bits.wp_Len

end results

end Perennial
