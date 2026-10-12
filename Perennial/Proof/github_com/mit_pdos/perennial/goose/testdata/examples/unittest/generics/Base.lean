/-
Shared definitions of the proofs of the goose generics unit tests: the `isPkgInit`s of
`generics` and `generics/helpers`, and the triple of the value-receiver method `Box.Get`
(`Box.wp_Get'`), which the pointer-receiver `(*Box).Get` (`Box.Get.spec`) calls.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.helpers
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Assumptions]

instance isPkgInit_helpers :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.helpers :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_helpers :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.helpers :=
  build_get_is_pkg_init_wf

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics :=
  build_get_is_pkg_init_wf

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics

section generic_proofs
variable {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {T : go.GoType}
  [IntoValTyped (GF := GF) T' T]

/-- The value-receiver method `Box.Get`. Kept as a shared lemma beside `Box.Get.spec`
(the pointer-receiver `(*Box).Get`, whose method set goose derives from this one), since a
Go method has one spec file `Box__Get`. -/
theorem Box.wp_Get' (b : Box T') :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (b @!! Box.ty T @!! go!"Get")) (Val #()))
    {{ RET #(b.Value'); True }} := by
  wp_start as _
  wp_auto
  wp_end

end generic_proofs

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics

end Perennial
