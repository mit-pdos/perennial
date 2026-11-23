/-
The proof of `math.Float64frombits`.
-/
module

public import Perennial.Spec.math.Float64frombits
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

theorem math.Float64frombits.wp_proof :
    math.Float64frombits.spec (GF := GF) (hG := hG) := by
  intro b
  wp_start
  wp_auto
  wp_end

end proof

end Perennial
