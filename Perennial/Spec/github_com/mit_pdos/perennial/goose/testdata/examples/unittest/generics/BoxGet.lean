/-
`generics.BoxGet`'s spec.
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

/-- `BoxGet[T](b)` returns `b.Value`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.BoxGet.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {T : go.GoType}
    [IntoValTyped (GF := GF) T' T] (b : Box T'),
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val #(functions BoxGet [T])) (Val #b))
    {{ RET #(b.Value'); True }}

end spec

end Perennial
