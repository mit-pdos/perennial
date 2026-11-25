/-
`math/rand.rngSource.Int63`'s spec.
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

/-- `(*rngSource).Int63()`, with the source's state: a non-negative `int64` (`Uint64()` masked to
63 bits); the state kept. -/
abbrev math.rand.rngSource.Int63.spec : Prop :=
  ∀ (p : Loc),
    {{ ownRngSource (GF := GF) (hG := hG) p }}
      (App (Val (p @!! go.GoType.PointerType rngSource.ty @!! go!"Int63")) (Val #()))
    {{ (x : w64), RET #x; ownRngSource p ∗ ⌜0 ≤ sint.Z x⌝ }}

end spec

end Perennial
