/-
`sort.StringSlice.Swap`'s spec.
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

/-- `x.Swap(i, j)` for `x` a `StringSlice` and indices `i`, `j` of it: `x[i]` and `x[j]`
exchanged. -/
abbrev sort.StringSlice.Swap.spec : Prop :=
  ∀ (x : GoSlice) (xs : List GoString) (i j : w64) (a b : GoString),
    0 ≤ sint.Z i → 0 ≤ sint.Z j → xs[sint.nat i]? = some a → xs[sint.nat j]? = some b →
    {{ (x ↦* xs : IProp GF) }}
      (App (App (Val (x @!! sort.StringSlice.ty @!! go!"Swap")) (Val #i)) (Val #j))
    {{ RET #(); x ↦* ((xs.set (sint.nat i) b).set (sint.nat j) a) }}

end spec

end Perennial
