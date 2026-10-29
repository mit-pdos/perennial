/-
`testLeafRoundTrip`'s spec (`goose/testdata/examples/unsafememory`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Pages

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Assumptions]

/-- `testLeafRoundTrip` returns `true`. Unlike `TestFunOk`, it assumes the package initialized: it calls `bytes` functions, whose specs need `bytes` initialized. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testLeafRoundTrip.spec : Prop :=
  ∀ Φ : val → IProp GF,
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory -∗
      Φ #true -∗
      WP (App (Val (@! testLeafRoundTrip)) (Val #())) {{ Φ }}

end spec

end Perennial
