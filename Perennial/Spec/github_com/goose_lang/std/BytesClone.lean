/-
`github.com/goose-lang/std.BytesClone`'s spec.
-/
module

public import Perennial.Proof.github_com.goose_lang.std.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

/-- `BytesClone(b)`: a fresh copy of the byte slice `b`. -/
abbrev github_com.goose_lang.std.BytesClone.spec : Prop :=
  ∀ (b : GoSlice) (xs : List w8) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std ∗ b ↦*{dq} xs }}
      (App (Val (@! BytesClone)) (Val #b))
    {{ (b' : GoSlice), RET #b'; b' ↦* xs ∗ ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end Perennial
