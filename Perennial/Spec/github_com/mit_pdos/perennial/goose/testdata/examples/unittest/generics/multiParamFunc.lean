/-
`generics.multiParamFunc`'s spec.
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

/-- `multiParamFunc[A, B](x, y)` returns the slice `[y]`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.multiParamFunc.spec : Prop :=
  ∀ {A' : Type} [ZeroVal A'] [TypedPointsto (GF := GF) A'] {A : go.GoType}
    [IntoValTyped (GF := GF) A' A]
    {B' : Type} [ZeroVal B'] [TypedPointsto (GF := GF) B'] {B : go.GoType}
    [IntoValTyped (GF := GF) B' B] (x : A') (y : B'),
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (App (Val #(functions multiParamFunc [A, B])) (Val #x)) (Val #y))
    {{ (s : GoSlice), RET #s; s ↦* [y] }}

end spec

end Perennial
