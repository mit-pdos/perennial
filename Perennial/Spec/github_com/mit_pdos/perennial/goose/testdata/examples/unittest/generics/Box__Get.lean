/-
`generics.(*Box).Get`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Base

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics

/-- `l.Get()` on a pointer `l` to a `Box[T]` returns the box's `Value`. (The value-receiver
form is the shared `Box.wp_Get'`.) -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Box.Get.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {T : go.GoType}
    [IntoValTyped (GF := GF) T' T] (l : Loc) (b : Box T'),
    {{ isPkgInit (PROP := IProp GF) pkg ∗ l ↦ b }}
      (App (Val (l @!! go.GoType.PointerType (Box.ty T) @!! go!"Get")) (Val #()))
    {{ RET #(b.Value'); True }}

end spec

end Perennial
