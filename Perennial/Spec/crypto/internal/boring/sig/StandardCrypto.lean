/-
`crypto/internal/boring/sig.StandardCrypto`'s spec.
-/
module

public import Perennial.Proof.crypto.internal.boring.sig.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.internal.boring.sig.Assumptions]

/-- `StandardCrypto()` (the trusted model of an assembly marker) returns. -/
abbrev crypto.internal.boring.sig.StandardCrypto.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.crypto.internal.boring.sig }}
    (App (Val (@! crypto.internal.boring.sig.StandardCrypto)) (Val #()))
  {{ RET #(); True }}

end spec

end Perennial
