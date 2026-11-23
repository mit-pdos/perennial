/-
`math/rand.Rand.Int31`'s spec.
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

/-- `r.Int31()`, of a generator over the runtime's source: a non-negative `int32`. -/
abbrev math.rand.Rand.Int31.spec : Prop :=
  ∀ (r : Loc),
    {{ isRuntimeRand (GF := GF) (hG := hG) r }}
      (App (Val (r @!! go.GoType.PointerType Rand.ty @!! go!"Int31")) (Val #()))
    {{ (x : w32), RET #x; ⌜0 ≤ sint.Z x⌝ }}

end spec

end Perennial
