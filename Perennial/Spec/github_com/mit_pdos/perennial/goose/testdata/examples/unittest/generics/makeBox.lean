/-
`generics.makeBox`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics

/-- `makeBox()` returns a `Box` holding `42`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.makeBox.spec : Prop :=
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! makeBox)) (Val #()))
    {{ RET #(Box.mk (W64 42)); True }}

end spec

end Perennial
