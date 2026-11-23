/-
The proof of `math.Float64bits`.
-/
module

public import Perennial.Spec.math.Float64bits
public import Perennial.Golang.Theory.Plain

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.Assumptions]

theorem math.Float64bits.wp_proof :
    math.Float64bits.spec (GF := GF) (hG := hG) := by
  intro f
  wp_start
  wp_auto
  wp_end

end proof

end Perennial
