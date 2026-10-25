/-
`internal.strconv.lower`'s spec.
-/
module

public import Perennial.Proof.internal.strconv.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.strconv.Assumptions]

/-- `lower(c)` is `c | ('x' - 'X')`, `c | 0x20`. -/
abbrev internal.strconv.lower.spec : Prop :=
  ∀ (c : w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.strconv }}
      (App (Val (@! lower)) (Val #c))
    {{ RET #(c ||| W8 32); True }}

end spec

end Perennial
