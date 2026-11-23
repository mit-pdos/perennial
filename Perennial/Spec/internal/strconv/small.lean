/-
`internal.strconv.small`'s spec.
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

/-- `small(i)` of `0 ≤ i < 100`: the decimal form of `i`. -/
abbrev internal.strconv.small.spec : Prop :=
  ∀ (i : w64), 0 ≤ sint.Z i → sint.Z i < 100 →
    {{ (True : IProp GF) }}
      (App (Val (@! small)) (Val #i))
    {{ RET #(internal.strconv.fmtUint i (W64 10)); True }}

end spec

end Perennial
