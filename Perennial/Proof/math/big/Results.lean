/-
Results of `math/big` derived from the linked ones: the spec of `(*Int).Int64` under its old
name `math.big.wp_Int64`.
-/
module

public import Perennial.Proof.math.big.Link

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.big.Assumptions]

/-- `(*Int).Int64` (`math.big.Int.wp_Int64`, under its old name). -/
theorem math.big.wp_Int64 : math.big.Int.Int64.spec (GF := GF) (hG := hG) :=
  math.big.Int.wp_Int64

end results

end Perennial
