/-
`math/rand.runtimeSource.Int63`'s spec.
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

/-- `(*runtimeSource).Int63()`: a non-negative `int64` (`runtime_rand()` masked to 63 bits). -/
abbrev math.rand.runtimeSource.Int63.spec : Prop :=
  ∀ (p : Loc),
    {{ (True : IProp GF) }}
      (App (Val (p @!! go.GoType.PointerType runtimeSource.ty @!! go!"Int63")) (Val #()))
    {{ (x : w64), RET #x; ⌜0 ≤ sint.Z x⌝ }}

end spec

end Perennial
