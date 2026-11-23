/-
`sort.StringSlice.Less`'s spec.
-/
module

public import Perennial.Proof.sort.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

/-- `x.Less(i, j)` for `x` a `StringSlice` and indices `i`, `j` of it: `x[i] < x[j]`, Go's
byte-wise string order. -/
abbrev sort.StringSlice.Less.spec : Prop :=
  ∀ (x : GoSlice) (xs : List GoString) (dq : DFrac) (i j : w64) (a b : GoString),
    0 ≤ sint.Z i → 0 ≤ sint.Z j → xs[sint.nat i]? = some a → xs[sint.nat j]? = some b →
    {{ (x ↦*{dq} xs : IProp GF) }}
      (App (App (Val (x @!! sort.StringSlice.ty @!! go!"Less")) (Val #i)) (Val #j))
    {{ RET #(decide (go.GoStringLt a b)); x ↦*{dq} xs }}

end spec

end Perennial
