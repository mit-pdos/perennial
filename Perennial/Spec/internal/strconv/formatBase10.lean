/-
`internal.strconv.formatBase10`'s spec.
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

/-- `formatBase10(a, u)` of a slice of at least 20 bytes: writes the decimal form of `u` to the end
of `a`, returning where it starts (it has at most 20 digits). -/
abbrev internal.strconv.formatBase10.spec : Prop :=
  ∀ (a : GoSlice) (xs : List w8) (u : w64), 20 ≤ xs.length →
    {{ (a ↦* xs : IProp GF) }}
      (App (App (Val (@! formatBase10)) (Val #a)) (Val #u))
    {{ (j : w64), RET #j;
        ⌜sint.Z j = xs.length - (internal.strconv.fmtUint u (W64 10)).length⌝ ∗
        a ↦* (xs.take (sint.nat j) ++ internal.strconv.fmtUint u (W64 10)) }}

end spec

end Perennial
