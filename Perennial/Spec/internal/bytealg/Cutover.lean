/-
`internal.bytealg.Cutover`'s spec.
-/
module

public import Perennial.Proof.internal.bytealg.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- `bytealg.Cutover(n)` returns some `int` (`(n + 16) / 8`); `Index` only uses it to decide
when to switch strategies, so its value does not matter. -/
abbrev internal.bytealg.Cutover.spec : Prop :=
  ∀ (n : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
      (App (Val (@! Cutover)) (Val #n))
    {{ (r : w64), RET #r; True }}

end spec

end Perennial
