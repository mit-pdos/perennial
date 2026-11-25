/-
`math/rand.rngSource.Uint64`'s spec.
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

/-- `(*rngSource).Uint64()`, with the source's state: some `uint64`; the state kept (its indices
stay in range). -/
abbrev math.rand.rngSource.Uint64.spec : Prop :=
  ∀ (p : Loc),
    {{ ownRngSource (GF := GF) (hG := hG) p }}
      (App (Val (p @!! go.GoType.PointerType rngSource.ty @!! go!"Uint64")) (Val #()))
    {{ (x : w64), RET #x; ownRngSource p }}

end spec

end Perennial
