/-
`math/rand.Int63n`'s spec.
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

/-- `rand.Int63n(n)` of a positive `n`: a number in `[0, n)` (Go panics for `n <= 0`). -/
abbrev math.rand.Int63n.spec : Prop :=
  ∀ (n : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand ∗ ⌜0 < sint.Z n⌝ }}
      (App (Val (@! Int63n)) (Val #n))
    {{ (x : w64), RET #x; ⌜0 ≤ sint.Z x ∧ sint.Z x < sint.Z n⌝ }}

end spec

end Perennial
