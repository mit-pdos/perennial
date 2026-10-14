/-
`internal.stringslite.IndexByte`'s spec.
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

/-- `stringslite.IndexByte(s, c)`: the index of the first `c` in `s`, or `-1`. -/
abbrev internal.stringslite.IndexByte.spec : Prop :=
  ∀ (s : GoString) (c : w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.stringslite }}
      (App (App (Val (@! IndexByte)) (Val #s)) (Val #c))
    {{ RET #(internal.bytealg.indexResult s [c]); True }}

end spec

end Perennial
