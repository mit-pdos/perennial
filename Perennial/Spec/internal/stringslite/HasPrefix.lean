/-
`internal.stringslite.HasPrefix`'s spec.
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

/-- `stringslite.HasPrefix(s, prefix)`: whether `s` begins with `prefix`. -/
abbrev internal.stringslite.HasPrefix.spec : Prop :=
  ∀ (s pfx : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.stringslite }}
      (App (App (Val (@! HasPrefix)) (Val #s)) (Val #pfx))
    {{ RET #(decide (pfx <+: s)); True }}

end spec

end Perennial
