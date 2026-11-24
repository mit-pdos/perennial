/-
The proof of `internal.gomodel.ChooseUint64`.
-/
module

public import Perennial.Spec.internal.gomodel.ChooseUint64

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.gomodel.Assumptions]

theorem internal.gomodel.ChooseUint64.wp_proof :
    internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply wp_ArbitraryInt as %x -
  wp_end

end proof

end Perennial
