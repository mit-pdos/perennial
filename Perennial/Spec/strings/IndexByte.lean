/-
`strings.IndexByte`'s spec.
-/
module

public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `strings.IndexByte(s, c)`: the index of the first `c` in `s`, or `-1`. -/
abbrev strings.IndexByte.spec : Prop :=
  ∀ (s : GoString) (c : w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! IndexByte)) (Val #s)) (Val #c))
    {{ RET #(internal.bytealg.indexResult s [c]); True }}

end spec

end Perennial
