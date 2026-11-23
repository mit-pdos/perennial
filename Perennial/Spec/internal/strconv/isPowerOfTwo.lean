/-
`internal.strconv.isPowerOfTwo`'s spec.
-/
module

public import Perennial.Proof.internal.strconv.FormatBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.strconv.Assumptions]

/-- `isPowerOfTwo(x)`: `x & (x - 1) == 0`. -/
abbrev internal.strconv.isPowerOfTwo.spec : Prop :=
  ∀ (x : w64),
    {{ (True : IProp GF) }}
      (App (Val (@! isPowerOfTwo)) (Val #x))
    {{ RET #(decide (x &&& (x - W64 1) = W64 0)); True }}

end spec

end Perennial
