/-
`internal.stringslite.Clone`'s spec.
-/
module

public import Perennial.Proof.internal.stringslite.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.stringslite.Assumptions]

/-- `stringslite.Clone(s)` returns `s` (a copy of its bytes, which as a value is `s` itself). -/
abbrev internal.stringslite.Clone.spec : Prop :=
  ∀ (s : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.stringslite }}
      (App (Val (@! Clone)) (Val #s))
    {{ RET #s; True }}

end spec

end Perennial
