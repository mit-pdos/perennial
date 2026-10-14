/-
`internal.bytealg.CountString`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- `bytealg.CountString(s, c)`: the number of `c`s in `s`. -/
abbrev internal.bytealg.CountString.spec : Prop :=
  ∀ (s : GoString) (c : w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
      (App (App (Val (@! CountString)) (Val #s)) (Val #c))
    {{ RET #(W64 (s.count c)); True }}

end spec

end Perennial
