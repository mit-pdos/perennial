/-
`internal.stringslite.TrimPrefix`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : internal.stringslite.Assumptions]

/-- `stringslite.TrimPrefix(s, prefix)`: `trimPrefix s prefix`. -/
abbrev internal.stringslite.TrimPrefix.spec : Prop :=
  ∀ (s pfx : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.stringslite }}
      (App (App (Val (@! TrimPrefix)) (Val #s)) (Val #pfx))
    {{ RET #(trimPrefix s pfx); True }}

end spec

end Perennial
