/-
`internal.stringslite.Index'`'s spec.
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

/-- `stringslite.Index(s, substr)`: the index of the first occurrence of `substr` in `s`, or
`-1`. -/
abbrev internal.stringslite.Index'.spec : Prop :=
  ∀ (s sub : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.stringslite }}
      (App (App (Val (@! Index')) (Val #s)) (Val #sub))
    {{ RET #(internal.bytealg.indexResult s sub); True }}

end spec

end Perennial
