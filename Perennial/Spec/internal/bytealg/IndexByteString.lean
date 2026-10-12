/-
`internal.bytealg.IndexByteString`'s spec.
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

/-- `bytealg.IndexByteString(s, c)`: the index of the first `c` in `s`, or `-1`. -/
abbrev internal.bytealg.IndexByteString.spec : Prop :=
  ∀ (s : GoString) (c : w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
      (App (App (Val (@! IndexByteString)) (Val #s)) (Val #c))
    {{ RET #(indexResult s [c]); True }}

end spec

end Perennial
