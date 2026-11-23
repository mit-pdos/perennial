/-
`math/rand.Rand.Int31n`'s spec.
-/
module

public import Perennial.Proof.math.rand.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.rand.Assumptions]

/-- `r.Int31n(n)`, of a generator over the runtime's source and a positive `n`: a number in
`[0, n)` (Go panics for `n <= 0`). -/
abbrev math.rand.Rand.Int31n.spec : Prop :=
  ∀ (r : Loc) (n : w32),
    {{ isRuntimeRand (GF := GF) (hG := hG) r ∗ ⌜0 < sint.Z n⌝ }}
      (App (Val (r @!! go.GoType.PointerType Rand.ty @!! go!"Int31n")) (Val #n))
    {{ (x : w32), RET #x; ⌜0 ≤ sint.Z x ∧ sint.Z x < sint.Z n⌝ }}

end spec

end Perennial
