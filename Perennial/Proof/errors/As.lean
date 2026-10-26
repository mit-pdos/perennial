/-
`errors.As`'s spec, assumed (`As` finds the target's type by reflection, which is not
translated; see the spec's docstring).
-/
module

public import Perennial.Spec.errors.As

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/-- Axiom: `As` and `as` use reflection throughout, which is not translated. -/
axiom errors.As.wp_proof : errors.As.spec (GF := GF) (hG := hG)

end proof

end Perennial
