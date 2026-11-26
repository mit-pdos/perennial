/-
`math/rand.NewSource`'s spec.
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

/-- `NewSource(seed)`: a `Source` holding a fresh `*rngSource`, with the source's state. -/
abbrev math.rand.NewSource.spec : Prop :=
  ∀ (seed : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
      (App (Val (@! NewSource)) (Val #seed))
    {{ (src : GoInterface), RET #src;
        ∃ p : Loc, ⌜src = interface.mkOk (go.PointerType rngSource.ty) #p⌝ ∗ ownRngSource p }}

end spec

end Perennial
