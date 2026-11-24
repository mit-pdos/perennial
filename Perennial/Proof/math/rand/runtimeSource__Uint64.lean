/-
The proof of `math/rand.runtimeSource.Uint64`.
-/
module

public import Perennial.Spec.math.rand.runtimeSource__Uint64
public import Perennial.Spec.math.rand.runtime_rand

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.rand.Assumptions]

theorem math.rand.runtimeSource.Uint64.wp_proof
    (wp_runtime_rand : math.rand.runtime_rand.spec (GF := GF) (hG := hG)) :
    math.rand.runtimeSource.Uint64.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  wp_auto
  wp_apply wp_runtime_rand as %y -
  wp_end

end proof

end Perennial
