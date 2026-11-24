/-
`crypto/internal/boring.Unreachable`'s spec.
-/
module

public import Perennial.Proof.crypto.internal.boring.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.internal.boring.Assumptions]

/-- `Unreachable()` (without BoringCrypto, `sig.StandardCrypto()`) returns. -/
abbrev crypto.internal.boring.Unreachable.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.crypto.internal.boring }}
    (App (Val (@! crypto.internal.boring.Unreachable)) (Val #()))
  {{ RET #(); True }}

end spec

end Perennial
