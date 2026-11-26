/-
`math/rand.rngSource.Seed`'s spec.
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

/-- `(*rngSource).Seed(seed)` on any `rngSource` value: the generator's state, its indices in range
(it reads the seeding table `rngCooked`, from the package's initialization). -/
abbrev math.rand.rngSource.Seed.spec : Prop :=
  ∀ (p : Loc) (v : rngSource) (seed : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand ∗ p ↦ v }}
      (App (Val (p @!! go.GoType.PointerType rngSource.ty @!! go!"Seed")) (Val #seed))
    {{ RET #(); ownRngSource p }}

end spec

end Perennial
