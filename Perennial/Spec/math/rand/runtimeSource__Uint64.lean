/-
`math/rand.runtimeSource.Uint64`'s spec.
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

/-- `(*runtimeSource).Uint64()`: some `uint64` (`runtime_rand()`). -/
abbrev math.rand.runtimeSource.Uint64.spec : Prop :=
  ∀ (p : Loc),
    {{ (True : IProp GF) }}
      (App (Val (p @!! go.GoType.PointerType runtimeSource.ty @!! go!"Uint64")) (Val #()))
    {{ (x : w64), RET #x; True }}

end spec

end Perennial
