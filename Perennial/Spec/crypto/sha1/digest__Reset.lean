/-
`crypto/sha1.(*digest).Reset`'s spec.
-/
module

public import Perennial.Proof.crypto.sha1.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.sha1.Assumptions]

/-- `d.Reset()` sets the state words to FIPS 180-4's initial ones and the counts to `0`: `d` has absorbed nothing. -/
abbrev crypto.sha1.digest.Reset.spec : Prop :=
  ∀ (d : Loc) (v : crypto.sha1.digest),
    {{ isPkgInit (PROP := IProp GF) pkg_id.crypto.sha1 ∗ d ↦ v }}
      (App (Val (d @!! go.GoType.PointerType crypto.sha1.digest.ty @!! go!"Reset")) (Val #()))
    {{ RET #(); ∃ v' : crypto.sha1.digest, d ↦ v' ∗ ⌜crypto.sha1.absorbed v' [] ∧ v'.x' = v.x'⌝ }}

end spec

end Perennial
