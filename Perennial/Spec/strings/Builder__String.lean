/-
`strings.Builder.String`'s spec.
-/
module

public import Perennial.Proof.strings.BuilderDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `b.String()` returns the bytes written. The model leaves them read-locked (so that a write
to them through a copy of the builder is stuck), so the builder is used up. -/
abbrev strings.Builder.String.spec : Prop :=
  ∀ (b : Loc) (s : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ ownBuilder b s }}
      (App (Val (b @!! go.GoType.PointerType Builder.ty @!! go!"String")) (Val #()))
    {{ RET #s; True }}

end spec

end Perennial
